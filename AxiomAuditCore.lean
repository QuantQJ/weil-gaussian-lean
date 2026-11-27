import FleetMollifierTail
import FleetGaussianDualCertificate
import FleetGaussianThreeProbe
import FleetThreeCentreInequality
import FleetDualInequality
import FleetDualConverse
import FleetTraceBoundRH
import FleetArithmeticBoundRH
import FleetPrimePoleBoundRH
import FleetPrimeSideConsequences
import FleetPrimeOnlyRH
import BoundaryTripleReal
import FleetLowZeroFree
import FleetMoebiusSmoothDecomposition
import FleetPrimeTarget
import FleetSquareBank
import FleetExponentLadder
import FleetHeatPositivityRH
import FleetPositivityDefect
import FleetTwoPointConvexity
import FleetWeilNonArch
import FleetSinhIdentity
import FleetDivisorCertificate
import FleetMultiplierFreedom
import FleetMoebiusTail
import FleetMoebiusTailBound
import FleetFiniteHeadRH
import FleetHeadContourZeta
import FleetHeadContourGauss
import FleetHeadContourLine
import FleetHeadContourShift
import FleetHeadContourLadder
import FleetHeadContourRH
import FleetHeadContourSubexp
import FleetHeadContourStrip
import FleetHeadContourConverse
import FleetStripAttempt
import FleetSraSmoothing
import FleetLandauTransfer
import FleetDaneshCriterion
import FleetTwistedWindowStrip
import FleetPsiStrip
import FleetWeilRH
import FleetSquarefreeError
import FleetDirichletZeroFree
import FleetLeastNonresidue
import FleetSmoothWindowStrip
import FleetExplicitPNT
import StripWidthDependency
import FleetSharpMidpointCertificate
import FleetEfficientArchimedeanDerivatives
import FleetEfficientMidpointCertificate
import FleetArchimedeanNumericalCertificate
import FleetRationalInterval
import FleetFastLogCertificate
import FleetDigammaEfficientCertificate
import FleetDigammaPointCertificate
import FleetConcreteDigammaEnclosures
import FleetEfficientArchimedeanCertificate
import FleetArchimedeanPointCertificate
import FleetGaussianFiniteClosedForm
import FleetMidpointQuadrature
import FleetMidpointDerivativeGrid
import FleetGaussianFiniteReduction
import FleetElementaryIntervalCertificate
import FleetElementaryNumericalInstances
import FleetGaussianPrimeTailCertificate
import FleetDigammaIntervalCertificate
import FleetIntervalQuadratureCertificate
import FleetGaussianArchimedeanNormalization
import FleetArchimedeanTailCertificate
import FleetSmoothPeriodization
import FleetPeriodizationSupport
import FleetPeriodicReplacement
import FleetGaussianMultiplier
import FleetGaussianPeriodizationTail
import FleetDampedPeriodicApproximation
import FleetGaussianUntwist
import FleetGaussianFiniteSpan
import FleetArithmeticLinearSpan
import FleetGaussianDensity
import FleetGaussianCriterion
import FleetFiniteGaussianFeasibility
import FleetRationalBanks
import FleetFiniteProbeCertificate
import FleetRationalBankCriterion
import FleetFiniteIntervalCertificate
import FleetStage100Witness
import FleetExponentialSpace
import FleetGaussianEnvelopeTail
import FleetGaussianDictionaryMember
import FleetPeriodicC2Density
import FleetFullLineFourier
import FleetExponentialEnvelope
import FleetPrimeFunctionalBound
import FleetExponentialFourierBound
import FleetFullLineArithmetic
import FleetArchimedeanFunctionalBound
import FleetFullLineLinearity
import FleetCompactExponentialBound
import FleetArithmeticContinuity
import FleetArithmeticDifference
import FleetExponentialDictionary
import FleetPeriodicApproximation
import FleetTrigPrimitive
import FleetTrigDensity
import FleetLinearDictionary
import FleetFiniteRealizationCriterion
import FleetEscapeExample
import FleetFiniteApproximation
import FleetGaussianTail
import FleetFiniteWindowEscape
import FleetLocalAtomicLimit
import FleetAtomicLimit
import FleetBlockBound
import FleetGlobalRealization
import FleetSeparatedExplicitFormula
import FleetSpectralTraceLimit
import FleetOffLineResponse
import FleetGammaDuplication
import GammaExplicitFormula
import HPProof
import FibonacciCore
import SpectralCompression
import GoldbachGate
import SHOSelfAdjoint
import SineBasis
import Semibounded
import PoincareSobolev
import HolderEquicontinuity
import BerryKeating
import XpDiscretization
import XpSpectrum
import SelfAdjointness
import Certification
import SierraXp
import SierraXpOperator
import RellichKondrachov
import SpectralFluctuation
import ExplicitFormula
import CascadeCounterexample
import Reduction
import Residue
import RectangleWinding
import RectangleResidue
import ZetaStrip
import ZetaLogDerivPole
import LogDerivResidue
import ZeroSymmetry
import PrimePowerSide
import L2Embedding
import ZerosCountable
import FunctionalEqLogDeriv
import ZetaConj
import ZetaGrowth
import HorizontalDecay
import ContourShift
import H2Algebra
import FiniteZeros
import PrincipalPartDischarge
import SegmentIntegrability
import ZeroSumConvergence
import Jensen
import ZetaGrowthNeg
import ZetaLowerBound
import ZeroDensity
import PartialFractions
import ZeroDensityUnconditional
import ZetaGrowthEM3
import ZeroAvoidingHeights
import LogDerivSegmentBound
import TestFunctions
import SegmentBoundUnconditional
import LeftLineBound
import PrimeSideLaplace
import ZeroSumLimit
import HorizontalVanishingSeq
import ExplicitFormulaZeroSide
import TraceInterface
import ExpSumLowerBound
import RealSideBound
import GaussianTest
import GaussianTraceFormula
import OffLineDetection
import TraceRealizationRH
import FleetDeBruijnNewman
import FleetSignUncertainty
import FleetFirstZero
import FleetWindowLowerBound
import FleetLaplacePole
import FleetWeightedLimit
import FleetWeightedFeasibilityRH
import FleetHeatMonotone
import FleetKroneckerSharpness
import FleetPositivityComposite
import FleetSmoothWindowLower

/-!
# Axiom audit — the project's receipt

Every line below must print a subset of `[propext, Classical.choice, Quot.sound]`
— Lean's three standard axioms. There are NO exceptions: the project
declares no `axiom`, uses no `sorry`, and uses no `native_decide`
(`Lean.ofReduceBool`). Run:

    lake build && lake env lean AxiomAudit.lean
-/

-- Discrete + continuum HP core (all standard axioms)
#print axioms hp_hermitian
#print axioms DiscreteSpectrum.dirichlet_laplacian_spectrum
#print axioms H1zero.ftc_repr
#print axioms H2.integration_by_parts
#print axioms DirichletLaplacian.symmetric
#print axioms hp_continuum_symmetric

-- Fibonacci / golden ratio core (all standard axioms)
#print axioms FibonacciCore.binet_formula
#print axioms FibonacciCore.lucas_binet
#print axioms FibonacciCore.cassini
#print axioms FibonacciCore.pell_lucas_fib
#print axioms FibonacciCore.golden_power_fib
#print axioms FibonacciCore.fib_ratio_tendsto_phi
#print axioms FibonacciCore.sqrt5_irrational
#print axioms FibonacciCore.phi_irrational
#print axioms FibonacciCore.fib_matrix_pow
#print axioms FibonacciCore.flagship_identity
#print axioms FibonacciCore.flagship_bound

-- Patent-support spectral compression claims (all standard axioms)
#print axioms SpectralCompression.geometric_spectrum_unique_of_two
#print axioms SpectralCompression.spectral_energy_bound
#print axioms SpectralCompression.spectral_tail_bound
#print axioms SpectralCompression.phi_spectrum_energy
#print axioms SpectralCompression.dct_row_sq_sum
#print axioms SpectralCompression.dct_rows_orthogonal

-- Goldbach gate: kernel `decide` (standard axioms)
#print axioms GoldbachGate.five_thirtyseven_spectral
#print axioms GoldbachGate.forty_two_has_tunnel
#print axioms GoldbachGate.no_tunnels_before_42
#print axioms GoldbachGate.forty_two_is_first_gate
#print axioms GoldbachGate.phi_pow_lt_seven_bound

-- SHO honest restatement
#print axioms SHO.symmetric_of_bounded_potential

-- Sine eigenbasis: orthogonality + completeness (2026-08-01)
#print axioms DiscreteSpectrum.sum_cos_eq
#print axioms DiscreteSpectrum.sineVec_orthogonal
#print axioms DiscreteSpectrum.sineVec_norm_sq
#print axioms DiscreteSpectrum.sineVec_orthogonal_basis

-- Semiboundedness: the Friedrichs hypotheses, machine-checked (2026-08-01)
#print axioms Semibounded.kinetic_energy_eq
#print axioms Semibounded.kinetic_energy_nonneg
#print axioms Semibounded.hp_form_semibounded
#print axioms Semibounded.hp_symmetric_H2
#print axioms Semibounded.eigenvalue_ge_neg_M
-- The continuum result: the Friedrichs hypothesis pair, proven; plus
-- orthogonality of eigenfunctions (a real spectral consequence of symmetry)
#print axioms hp_continuum_friedrichs_hypotheses
#print axioms eigenfunctions_orthogonal
#print axioms hp_complete
#print axioms hp_discrete_self_adjoint

-- Sobolev embedding, Poincare, coercivity (2026-08-01)
#print axioms PoincareSobolev.sq_intervalIntegral_le
#print axioms PoincareSobolev.sobolev_pointwise_sq
#print axioms PoincareSobolev.sobolev_sup_bound
#print axioms PoincareSobolev.poincare
#print axioms PoincareSobolev.hp_form_coercive

-- Holder-1/2 + Arzela-Ascoli inputs (1-D Rellich-Kondrachov analysis)
#print axioms HolderEquicontinuity.increment_eq
#print axioms HolderEquicontinuity.holder_half_sq
#print axioms HolderEquicontinuity.holder_half
#print axioms HolderEquicontinuity.holder_uniform
#print axioms HolderEquicontinuity.ascoli_inputs

-- Berry-Keating xp: an operator class with the right spectral DENSITY
-- (smooth term only -- says nothing about the arithmetic / RH)
#print axioms BerryKeating.hyperbolic_area
#print axioms BerryKeating.bk_matches_riemann_vonMangoldt
#print axioms BerryKeating.bk_density_exceeds_quadratic
#print axioms BerryKeating.bk_eigenvalue_growth_subquadratic

-- xp discretization: why naive xp has continuous spectrum, and why a
-- fixed-length compactification gives the WRONG density
#print axioms XpDiscretization.dilation_hasDerivAt
#print axioms XpDiscretization.dilation_log_identity
#print axioms XpDiscretization.fixed_length_compactification_fails
#print axioms XpDiscretization.no_circumference_matches_density
#print axioms XpDiscretization.effective_length_grows

-- Bohr-Sommerfeld quantization of the xp area: a spectrum with the
-- Riemann-von Mangoldt density and the zeta growth envelope
#print axioms XpSpectrum.A_hasDerivAt
#print axioms XpSpectrum.A_strictMonoOn
#print axioms XpSpectrum.quantization_growth_envelope
#print axioms XpSpectrum.quantized_subquadratic

-- Sierra truncated xp: energy-dependent cutoff (2026-09-12)
#print axioms SierraXp.truncationLength_pos
#print axioms SierraXp.fixed_truncation_density_fails
#print axioms SierraXp.cutoffLength_eq_effective
#print axioms SierraXp.sierraCount_cutoff
#print axioms SierraXp.energy_dependent_matches_rvm_leading
#print axioms SierraXp.log_is_smooth_density_candidate
#print axioms SierraXp.spectrum_match_still_open

-- Certification: φ, Fibonacci, Lucas, Cassini, matrix form (standard axioms)
#print axioms Certification.binet_formula
#print axioms Certification.lucas_binet
#print axioms Certification.golden_power_fib
#print axioms Certification.cassini
#print axioms Certification.pell_lucas_fib
#print axioms Certification.fib_matrix_pow
#print axioms Certification.fib_matrix_diagonalization
#print axioms Certification.fib_lucas_on_hyperbola
#print axioms Certification.the_complete_picture

-- Sierra self-adjoint density realization (2026-09-12)
#print axioms SierraXpOperator.modelMatrix_selfAdjoint
#print axioms SierraXpOperator.densityRealization_exists
#print axioms SierraXpOperator.energyDependentDensityRealization_exists
#print axioms SierraXpOperator.modeBudget_le_sierra
#print axioms SierraXpOperator.modeBudget_abs_err_lt_one
#print axioms SierraXpOperator.single_continuum_still_open

-- 1-D Rellich–Kondrachov via Arzelà–Ascoli, and discreteness of the
-- spectrum without self-adjointness (2026-09-12)
#print axioms RellichKondrachov.uniform_subseq
#print axioms RellichKondrachov.l2_cauchy_subseq
#print axioms RellichKondrachov.energy_le_of_eigen
#print axioms RellichKondrachov.no_infinite_orthonormal_eigen_below
#print axioms RellichKondrachov.eigenvalues_tendsto_atTop

-- Fluctuation term: Bohr–Sommerfeld spectra have |S(E)| ≤ 1, so an unbounded
-- fluctuation (the zeta S(T), cited as hypothesis) rules them out (2026-09-12)
#print axioms SpectralFluctuation.count_eq_of_mem_cell
#print axioms SpectralFluctuation.abs_fluct_le_one
#print axioms SpectralFluctuation.fluct_bounded
#print axioms SpectralFluctuation.not_bohrSommerfeld_of_unbounded_fluct
#print axioms SpectralFluctuation.lam_unique
#print axioms SpectralFluctuation.berryKeating_fluct_le_one
#print axioms SpectralFluctuation.berryKeating_monoA_of_one_le

-- Explicit formula, arithmetic half: zeta side on Re s = c > 1 equals the
-- prime side Σ Λ(n) n^{-c} 𝓕g(log n), by dominated convergence (2026-09-12)
#print axioms ExplicitFormula.coeff_summable
#print axioms ExplicitFormula.term_eq
#print axioms ExplicitFormula.hasSum_line
#print axioms ExplicitFormula.hasSum_primeSide
#print axioms ExplicitFormula.vertical_line_eq_prime_sum
#print axioms ExplicitFormula.primeSide_summable
#print axioms ExplicitFormula.explicit_formula_arithmetic_half

-- Crossing the fluctuation barrier is cheap: a self-adjoint exponential
-- cascade does it, so "unbounded fluctuation" is not the prize property (2026-09-12)
#print axioms CascadeCounterexample.count_cascade_le
#print axioms CascadeCounterexample.cascade_crosses
#print axioms CascadeCounterexample.barrier_crossing_is_cheap

-- Hilbert–Pólya reduction: the interface between operators and zeros (2026-09-12)
#print axioms Reduction.riemannHypothesis_iff
#print axioms Reduction.riemannHypothesis_of_ordinates_real
#print axioms Reduction.hilbert_polya_reduction
#print axioms Reduction.hilbert_polya_reduction_selfAdjoint
#print axioms Reduction.hilbert_polya_reduction_operator
#print axioms Reduction.zeroSide_iff_arithmeticTrace
#print axioms Reduction.ordinate_spectrum_implies_RH
#print axioms Reduction.isOrdinateSpectrum_realizes

-- Fleet 1 (2026-09-12): rectangle residue theorem, zeta zero facts, prime-power side, L² embedding
-- Residue
#print axioms Residue.SegmentIntegrable.sub
#print axioms Residue.SegmentIntegrable.const_mul
#print axioms Residue.intervalIntegrable_finset_sum
#print axioms Residue.SegmentIntegrable.sum
#print axioms Residue.rectBoundaryIntegral_eq_zero_of_differentiableOn
#print axioms Residue.rectBoundaryIntegral_sub
#print axioms Residue.rectBoundaryIntegral_const_mul
#print axioms Residue.rectBoundaryIntegral_finset_sum
#print axioms Residue.principalPart_eq
#print axioms Residue.rectBoundaryIntegral_eq_sum_residue_mul_winding
-- RectangleWinding
#print axioms RectangleWinding.horiz_mem_slitPlane
#print axioms RectangleWinding.vertRight_mem_slitPlane
#print axioms RectangleWinding.vertLeft_mem_slitPlane
#print axioms RectangleWinding.hasDerivAt_ofReal
#print axioms RectangleWinding.hasDerivAt_horiz
#print axioms RectangleWinding.hasDerivAt_vert
#print axioms RectangleWinding.hasDerivAt_vertReflected
#print axioms RectangleWinding.integral_horiz
#print axioms RectangleWinding.integral_vert_right
#print axioms RectangleWinding.integral_vert_left
#print axioms RectangleWinding.log_sub_log_neg_of_im_pos
#print axioms RectangleWinding.log_sub_log_neg_of_im_neg
#print axioms RectangleWinding.rect_winding
-- RectangleResidue
#print axioms RectangleResidue.rectBoundaryIntegral_eq_rectInt
#print axioms RectangleResidue.rectBoundaryIntegral_eq_rectInt'
#print axioms RectangleResidue.intervalIntegrable_inv_sub_horiz
#print axioms RectangleResidue.intervalIntegrable_inv_sub_vert
#print axioms RectangleResidue.segmentIntegrable_inv_sub_of_mem_interior
#print axioms RectangleResidue.rectBoundaryIntegral_inv_sub_eq_two_pi_I
#print axioms RectangleResidue.rectangle_residue_simplePoles
#print axioms RectangleResidue.rectangle_residue_simplePoles'
-- ZetaStrip
#print axioms ZetaStrip.re_lt_one_of_isNontrivialZero
#print axioms ZetaStrip.ne_zero_of_isNontrivialZero
#print axioms ZetaStrip.re_pos_of_isNontrivialZero
#print axioms ZetaStrip.mem_strip_of_isNontrivialZero
-- ZetaLogDerivPole
#print axioms ZetaLogDerivPole.differentiable_zetaReg
#print axioms ZetaLogDerivPole.riemannZeta_eq_zetaReg_add
#print axioms ZetaLogDerivPole.hasDerivAt_riemannZeta_of_ne_one
#print axioms ZetaLogDerivPole.tendsto_sub_one_mul_logDeriv_zeta
-- LogDerivResidue
#print axioms LogDerivResidue.continuousAt_deriv_of_analyticAt
#print axioms LogDerivResidue.deriv_eq_of_eventually_eq_pow_mul
#print axioms LogDerivResidue.tendsto_sub_mul_logDeriv
#print axioms LogDerivResidue.tendsto_sub_mul_logDeriv_simple_zero
-- ZeroSymmetry
#print axioms ZeroSymmetry.bernoulli_two_mul_ne_zero
#print axioms ZeroSymmetry.riemannZeta_neg_odd_ne_zero
#print axioms ZeroSymmetry.ne_neg_nat_of_isNontrivialZero
#print axioms ZeroSymmetry.isNontrivialZero_one_sub
#print axioms ZeroSymmetry.isNontrivialZero_iff_one_sub
-- PrimePowerSide
#print axioms PrimePowerSide.coeff_eq_zero_of_not_isPrimePow
#print axioms PrimePowerSide.support_coeff_subset
#print axioms PrimePowerSide.coeff_prime_pow
#print axioms PrimePowerSide.term_eq_zero_of_not_isPrimePow
#print axioms PrimePowerSide.support_term_subset
#print axioms PrimePowerSide.primeSide_eq_tsum_primePow
#print axioms PrimePowerSide.primePow_summable
#print axioms PrimePowerSide.pairToNat_isPrimePow
#print axioms PrimePowerSide.pairToNat_injective
#print axioms PrimePowerSide.range_pairToNat
#print axioms PrimePowerSide.term_pair
#print axioms PrimePowerSide.primeSide_eq_tsum_prime_pnat
#print axioms PrimePowerSide.prime_pnat_summable
-- L2Embedding
#print axioms L2Embedding.inner_toL2
#print axioms L2Embedding.norm_sq_toL2
#print axioms L2Embedding.orthogonal_of_eigen
-- ZerosCountable
#print axioms ZerosCountable.countable_of_forall_isolated
#print axioms ZerosCountable.analyticOnNhd_riemannZeta
#print axioms ZerosCountable.isPreconnected_compl_singleton_one
#print axioms ZerosCountable.riemannZeta_two_ne_zero
#print axioms ZerosCountable.isolated_zero_riemannZeta
#print axioms ZerosCountable.isolated_of_isNontrivialZero
#print axioms ZerosCountable.countable_nontrivialZeros
#print axioms ZerosCountable.exists_enumeration_nontrivialZeros

-- Fleet 2 (2026-09-12): functional-equation log-derivative, ζ conjugation, growth bounds, horizontal decay, contour shift, H² algebra
-- FunctionalEqLogDeriv
#print axioms FunctionalEqLogDeriv.eventually_ne_neg_nat
#print axioms FunctionalEqLogDeriv.hasDerivAt_zeta_one_sub
#print axioms FunctionalEqLogDeriv.two_pi_ne_zero
#print axioms FunctionalEqLogDeriv.log_two_pi_eq
#print axioms FunctionalEqLogDeriv.hasDerivAt_functionalEq_rhs
#print axioms FunctionalEqLogDeriv.deriv_zeta_one_sub
#print axioms FunctionalEqLogDeriv.logDeriv_zeta_one_sub
-- ZetaConj
#print axioms ZetaConj.hasDerivAt_conj_comp_conj
#print axioms ZetaConj.differentiable_conj_comp_conj
#print axioms ZetaConj.natCast_cpow_conj
#print axioms ZetaConj.riemannZeta_conj_of_one_lt_re
#print axioms ZetaConj.Gammaℝ_conj
#print axioms ZetaConj.completedRiemannZeta₀_conj_of_one_lt_re
#print axioms ZetaConj.completedRiemannZeta₀_conj
#print axioms ZetaConj.completedRiemannZeta_conj
#print axioms ZetaConj.riemannZeta_conj
#print axioms ZetaConj.isNontrivialZero_conj
-- ZetaGrowth
#print axioms ZetaGrowth.norm_zeta_le_tsum_of_re_ge
#print axioms ZetaGrowth.norm_zeta_real_eq
#print axioms ZetaGrowth.norm_zeta_le_of_re_ge
#print axioms ZetaGrowth.norm_logDeriv_zeta_le_of_re_ge
#print axioms ZetaGrowth.norm_ofReal_cpow
#print axioms ZetaGrowth.norm_emTerm_le
#print axioms ZetaGrowth.summable_add_one_rpow
#print axioms ZetaGrowth.summable_emTerm
#print axioms ZetaGrowth.sum_emTerm
#print axioms ZetaGrowth.emTerm_differentiableAt
#print axioms ZetaGrowth.zetaAbel_differentiableOn
#print axioms ZetaGrowth.zetaAbel_eq_zeta_of_one_lt_re
#print axioms ZetaGrowth.eqOn_zeta_zetaAbel_of_convex
#print axioms ZetaGrowth.zeta_eq_zetaAbel
#print axioms ZetaGrowth.rpow_add_one_le_telescope
#print axioms ZetaGrowth.tsum_add_one_rpow_le
#print axioms ZetaGrowth.K_le_three
#print axioms ZetaGrowth.norm_zeta_le_of_half_le_re_K
#print axioms ZetaGrowth.norm_zeta_le_of_half_le_re
#print axioms ZetaGrowth.zeta_growth_strip
#print axioms ZetaGrowth.exists_zeta_growth_strip
#print axioms ZetaGrowth.zeta_growth_line
#print axioms ZetaGrowth.zeta_eq_sum_add_tail
#print axioms ZetaGrowth.rpow_neg_half_le_telescope
#print axioms ZetaGrowth.sum_add_one_rpow_neg_half_le
#print axioms ZetaGrowth.rpow_neg_three_half_le_telescope
#print axioms ZetaGrowth.tsum_tail_rpow_le
#print axioms ZetaGrowth.summable_add_rpow
#print axioms ZetaGrowth.norm_zeta_le_split
#print axioms ZetaGrowth.zeta_growth_strip_sqrt
#print axioms ZetaGrowth.zeta_growth_strip_rpow
#print axioms ZetaGrowth.zeta_growth_line_rpow
-- HorizontalDecay
#print axioms HorizontalDecay.horizontal_integral_norm_le
#print axioms HorizontalDecay.horizontal_integral_tendsto_zero_filter
#print axioms HorizontalDecay.horizontal_integral_tendsto_zero
#print axioms HorizontalDecay.horizontal_integral_tendsto_zero_atBot
#print axioms HorizontalDecay.log_sq_le_sq
#print axioms HorizontalDecay.log_sq_mul_exp_neg_tendsto_zero
#print axioms HorizontalDecay.log_sq_mul_exp_tendsto_zero_atBot
#print axioms HorizontalDecay.horizontal_integral_tendsto_zero_of_log_sq_exp
#print axioms HorizontalDecay.horizontal_integral_tendsto_zero_of_log_sq_exp_atBot
-- ContourShift
#print axioms ContourShift.rectBoundaryIntegral_eq_of_extension
#print axioms ContourShift.poleSet_injOn
#print axioms ContourShift.one_pole_not_mem_image
#print axioms ContourShift.sum_residue_poleSet
#print axioms ContourShift.principalPart_poleSet
#print axioms ContourShift.closedRect_mem_nhds
#print axioms ContourShift.one_mem_openRect
#print axioms ContourShift.differentiableOn_regularPart
#print axioms ContourShift.F_eq_regularPart_add_principalPart
#print axioms ContourShift.mem_openRect_of_isNontrivialZero
#print axioms ContourShift.one_not_mem_of_isNontrivialZero
#print axioms ContourShift.contour_shift_rectangle
#print axioms ContourShift.vertical_lines_difference
-- H2Algebra
#print axioms H2.glue_eq_of_mem_Icc
#print axioms H2.glue_eq_of_mem_Iic
#print axioms H2.glue_eq_of_mem_Ici
#print axioms H2.intervalIntegrable_of_eqOn_Ioo
#print axioms H2.ofInterior_f_eq
#print axioms H2.ofInterior_deriv_eq
#print axioms H2.add_f_eq
#print axioms H2.add_deriv_eq
#print axioms H2.smul_f_eq
#print axioms H2.zero_f_eq
#print axioms H2.add_def
#print axioms H2.smul_def
#print axioms H2.zero_def
#print axioms H2Algebra.toL2_add
#print axioms H2Algebra.toL2_add'
#print axioms H2Algebra.toL2_smul
#print axioms H2Algebra.toL2_zero
#print axioms H2Algebra.inner_toL2_add_left
#print axioms H2Algebra.inner_toL2_smul_left
#print axioms H2Algebra.inner_toL2_add_right
#print axioms H2Algebra.integral_add_mul

-- Fleet 3 (2026-09-12): finite zeros, principal-part discharge, segment integrability, zero-sum convergence, Jensen
-- FiniteZeros
#print axioms FiniteZeros.eventually_ne_zero_nhdsNE_one
#print axioms FiniteZeros.eventually_ne_zero_nhdsNE
#print axioms FiniteZeros.zeros_ne_one_isClosed_and_discrete
#print axioms FiniteZeros.finite_zeros_ne_one_of_isCompact
#print axioms FiniteZeros.finite_zeros_of_isCompact
#print axioms FiniteZeros.finite_nontrivialZeros_of_isCompact
#print axioms FiniteZeros.isCompact_rect
#print axioms FiniteZeros.finite_zeros_rect
-- PrincipalPartDischarge
#print axioms PrincipalPartDischarge.differentiable_zetaNum
#print axioms PrincipalPartDischarge.zetaNum_one
#print axioms PrincipalPartDischarge.riemannZeta_eq_zetaNum_div
#print axioms PrincipalPartDischarge.deriv_riemannZeta_of_ne_one
#print axioms PrincipalPartDischarge.logDeriv_zeta_eventually_eq_near_one
#print axioms PrincipalPartDischarge.eventually_ne_zero_punctured
#print axioms PrincipalPartDischarge.finite_zeros_of_isCompact
#print axioms PrincipalPartDischarge.isCompact_rect
#print axioms PrincipalPartDischarge.mem_zeroFinset
#print axioms PrincipalPartDischarge.one_not_mem_zeroFinset
#print axioms PrincipalPartDischarge.analyticAt_riemannZeta_of_ne_one
#print axioms PrincipalPartDischarge.not_eventually_zero
#print axioms PrincipalPartDischarge.exists_factorization
#print axioms PrincipalPartDischarge.zetaOrder_pos
#print axioms PrincipalPartDischarge.logDeriv_eventually_eq_of_eventually_eq_pow_mul
#print axioms PrincipalPartDischarge.tendsto_sub_principalPart
#print axioms PrincipalPartDischarge.eventually_not_mem_punctured
#print axioms PrincipalPartDischarge.exists_differentiableAt_of_tendsto_punctures
#print axioms PrincipalPartDischarge.coef_one
#print axioms PrincipalPartDischarge.coef_of_ne_one
#print axioms PrincipalPartDischarge.mem_punctures
#print axioms PrincipalPartDischarge.one_mem_punctures
#print axioms PrincipalPartDischarge.sum_coef_punctures
#print axioms PrincipalPartDischarge.naiveRemainder_differentiableAt
#print axioms PrincipalPartDischarge.eventually_differentiableAt_naiveRemainder
#print axioms PrincipalPartDischarge.exists_tendsto_naiveRemainder
#print axioms PrincipalPartDischarge.exists_remainder_differentiableAt
#print axioms PrincipalPartDischarge.exists_holomorphic_remainder
#print axioms PrincipalPartDischarge.zetaOrder_pos_of_mem_zeroFinset
#print axioms PrincipalPartDischarge.contour_shift_rectangle_of_G
#print axioms PrincipalPartDischarge.vertical_lines_difference_of_G
-- SegmentIntegrability
#print axioms SegmentIntegrability.ne_one_of_mem_boundary
#print axioms SegmentIntegrability.mem_boundary_iff
#print axioms SegmentIntegrability.continuousAt_deriv_riemannZeta
#print axioms SegmentIntegrability.continuousAt_logDeriv_riemannZeta
#print axioms SegmentIntegrability.continuousOn_F_boundary
#print axioms SegmentIntegrability.intervalIntegrable_F_comp
#print axioms SegmentIntegrability.intervalIntegrable_bottom
#print axioms SegmentIntegrability.intervalIntegrable_top
#print axioms SegmentIntegrability.intervalIntegrable_right
#print axioms SegmentIntegrability.intervalIntegrable_left
#print axioms SegmentIntegrability.segmentIntegrable_F
#print axioms SegmentIntegrability.segmentIntegrable_F_of_differentiableOn
#print axioms SegmentIntegrability.eventually_ne_zero_nhdsWithin_one
#print axioms SegmentIntegrability.eventually_ne_zero_nhdsWithin
#print axioms SegmentIntegrability.finite_zerosBox
#print axioms SegmentIntegrability.exists_T_avoiding_zeros
#print axioms SegmentIntegrability.exists_T_avoiding_zeros'
#print axioms SegmentIntegrability.boundary_nonvanishing_of_edges
-- ZeroSumConvergence
#print axioms ZeroSumConvergence.count_ge_succ
#print axioms ZeroSumConvergence.count_bound_const_pos
#print axioms ZeroSumConvergence.abs_rpow_three_halves_ge
#print axioms ZeroSumConvergence.inv_sq_le
#print axioms ZeroSumConvergence.summable_inv_sq_of_count_bound
#print axioms ZeroSumConvergence.summable_norm_of_decay
#print axioms ZeroSumConvergence.summable_of_decay
#print axioms ZeroSumConvergence.tendsto_partial_sums
-- Jensen
#print axioms Jensen.integral_circleMap_eq_two_pi_mul
#print axioms Jensen.integral_re_circleMap_eq_two_pi_mul
#print axioms Jensen.circle_mean_value
#print axioms Jensen.differentiableOn_log_comp_of_mem_slitPlane
#print axioms Jensen.norm_sq_sub_conj_mul_of_mem_sphere
#print axioms Jensen.integral_log_norm_circleMap_sub_of_mem_ball
#print axioms Jensen.integral_log_norm_circleMap_sub_of_not_mem_closedBall
#print axioms Jensen.hasDerivAt_primitive_of_hasFPowerSeriesOnBall
#print axioms Jensen.exists_hasFPowerSeriesOnBall_of_differentiableOn_ball
#print axioms Jensen.exists_differentiableOn_exp_eq_of_ne_zero
#print axioms Jensen.log_norm_eq_sum_add_log_norm
#print axioms Jensen.jensen_formula_multiplicity
#print axioms Jensen.jensen_formula
#print axioms Jensen.sum_mult_mul_log_two_le_log
#print axioms Jensen.card_mul_log_two_le_log
#print axioms Jensen.card_zeros_le_log_div_log_two
#print axioms Jensen.exists_factorization_of_finite_zeros
#print axioms Jensen.jensen_formula_of_finite_zeros
#print axioms Jensen.card_zeros_le_log_div_log_two_of_finite_zeros

-- Fleet 4 (2026-09-12): ζ growth for Re s > -1, Euler-product lower bound, zero density via Jensen, Borel–Carathéodory partial fractions
-- ZetaGrowthNeg
#print axioms ZetaGrowthNeg.abs_bern₂_le
#print axioms ZetaGrowthNeg.emTerm₂_eq_emAnti
#print axioms ZetaGrowthNeg.emAnti_hasDerivAt
#print axioms ZetaGrowthNeg.norm_emTerm₂_le
#print axioms ZetaGrowthNeg.summable_emTerm₂
#print axioms ZetaGrowthNeg.emTerm₂_differentiableAt
#print axioms ZetaGrowthNeg.sum_emTerm₂_eq
#print axioms ZetaGrowthNeg.sum_emTerm₂
#print axioms ZetaGrowthNeg.tendsto_add_one_cpow_zero
#print axioms ZetaGrowthNeg.zetaAbel₂_eq_zetaAbel
#print axioms ZetaGrowthNeg.zetaAbel₂_differentiableOn
#print axioms ZetaGrowthNeg.eqOn_zeta_zetaAbel₂_of_convex
#print axioms ZetaGrowthNeg.zeta_eq_zetaAbel₂
#print axioms ZetaGrowthNeg.zeta_eq_sum_add_tail₂
#print axioms ZetaGrowthNeg.norm_zeta_le_split₂
#print axioms ZetaGrowthNeg.one_le_of_two_le_mul_self
#print axioms ZetaGrowthNeg.le_mul_self_of_one_le
#print axioms ZetaGrowthNeg.mul_self_le_cube_of_one_le
#print axioms ZetaGrowthNeg.poly_bound_aux
#print axioms ZetaGrowthNeg.quart_le_aux
#print axioms ZetaGrowthNeg.zeta_growth_wide_bound
#print axioms ZetaGrowthNeg.zeta_growth_neg_strip
#print axioms ZetaGrowthNeg.zeta_growth_wide
#print axioms ZetaGrowthNeg.zeta_growth_wide_of_sqrt
-- ZetaLowerBound
#print axioms ZetaLowerBound.norm_prime_cpow_neg
#print axioms ZetaLowerBound.summable_primes_rpow
#print axioms ZetaLowerBound.prime_rpow_neg_lt_one
#print axioms ZetaLowerBound.prime_rpow_neg_pos
#print axioms ZetaLowerBound.summable_neg_log_one_sub
#print axioms ZetaLowerBound.re_neg_log_eq_logTerm
#print axioms ZetaLowerBound.summable_logTerm
#print axioms ZetaLowerBound.norm_zeta_eq_exp_tsum_logTerm
#print axioms ZetaLowerBound.one_sub_prime_cpow_ofReal
#print axioms ZetaLowerBound.logTerm_ofReal
#print axioms ZetaLowerBound.logTerm_two_le
#print axioms ZetaLowerBound.norm_zeta_two_re_le_mul
#print axioms ZetaLowerBound.norm_zeta_real_pos
#print axioms ZetaLowerBound.one_le_norm_zeta_real
#print axioms ZetaLowerBound.norm_zeta_ge_of_one_lt_re
#print axioms ZetaLowerBound.inv_norm_zeta_re_le_norm_zeta
#print axioms ZetaLowerBound.norm_zeta_three_halves_le_three
#print axioms ZetaLowerBound.norm_zeta_three_halves_ge
#print axioms ZetaLowerBound.norm_zeta_ge_third_of_re_eq_three_halves
-- ZeroDensity
#print axioms ZeroDensity.card_mul_log_le_of_jensen
#print axioms ZeroDensity.ncard_mul_log_le_of_jensen
#print axioms ZeroDensity.norm_le_of_re_im
#print axioms ZeroDensity.finite_zeros_im_mem_Icc
#print axioms ZeroDensity.finite_zeros_abs_im_le
#print axioms ZeroDensity.finite_zeros_near_height
#print axioms ZeroDensity.isNontrivialZero_one_sub_conj
#print axioms ZeroDensity.one_sub_conj_re
#print axioms ZeroDensity.one_sub_conj_im
#print axioms ZeroDensity.K_nonneg
#print axioms ZeroDensity.norm_riemannZeta_two_le
#print axioms ZeroDensity.ncard_zeros_right_near_height_le
#print axioms ZeroDensity.ncard_zeros_near_height_le
#print axioms ZeroDensity.ncard_zeros_step
#print axioms ZeroDensity.ncard_zeros_le_of_nat
#print axioms ZeroDensity.count_le_T_log_T
#print axioms ZeroDensity.finite_index_of_height
#print axioms ZeroDensity.count_le_ncard
#print axioms ZeroDensity.zeroSumConvergence_hypotheses
#print axioms ZeroDensity.summable_inv_sq_ordinates
-- PartialFractions
#print axioms PartialFractions.norm_lt_norm_two_mul_sub_of_re_lt
#print axioms PartialFractions.norm_le_of_re_lt
#print axioms PartialFractions.borel_caratheodory
#print axioms PartialFractions.borel_caratheodory_closedBall
#print axioms PartialFractions.norm_deriv_le_of_forall_mem_closedBall_norm_le
#print axioms PartialFractions.exists_log_normalized
#print axioms PartialFractions.norm_logDeriv_le_of_norm_le
#print axioms PartialFractions.norm_logDeriv_sub_sum_le_of_factorization
#print axioms PartialFractions.norm_logDeriv_sub_sum_le_of_factorization'
#print axioms PartialFractions.exists_radius_lt_of_forall_mem_ball
#print axioms PartialFractions.exists_extension_of_factorization
#print axioms PartialFractions.norm_logDeriv_sub_sum_le_of_finite_zeros
#print axioms PartialFractions.norm_logDeriv_sub_sum_le_of_finite_zeros'

-- Zero density, unconditional (glue of ZeroDensity + ZetaGrowthNeg + ZetaLowerBound)
#print axioms ZeroDensityUnconditional.ncard_zeros_near_height_le
#print axioms ZeroDensityUnconditional.count_le_T_log_T
#print axioms ZeroDensityUnconditional.summable_inv_sq_ordinates
#print axioms ZeroDensityUnconditional.zeroSumConvergence_hypotheses

-- Fleet 5 (2026-09-12): ζ continued to Re s > -3, zero-avoiding heights, ζ'/ζ segment bounds, test functions
-- ZetaGrowthEM3
#print axioms ZetaGrowthEM3.abs_bern₄_le
#print axioms ZetaGrowthEM3.emTerm₄_eq_emAnti₄
#print axioms ZetaGrowthEM3.emAnti₄_hasDerivAt
#print axioms ZetaGrowthEM3.norm_emTerm₄_le
#print axioms ZetaGrowthEM3.summable_emTerm₄
#print axioms ZetaGrowthEM3.emTerm₄_differentiableAt
#print axioms ZetaGrowthEM3.sum_emTerm₄_eq
#print axioms ZetaGrowthEM3.sum_emTerm₄
#print axioms ZetaGrowthEM3.zetaAbel₄_eq_zetaAbel₂
#print axioms ZetaGrowthEM3.zetaAbel₄_differentiableOn
#print axioms ZetaGrowthEM3.eqOn_zeta_zetaAbel₄_of_convex
#print axioms ZetaGrowthEM3.zeta_eq_zetaAbel₄
#print axioms ZetaGrowthEM3.zeta_eq_sum_add_tail₄
#print axioms ZetaGrowthEM3.norm_zeta_le_split₄
#print axioms ZetaGrowthEM3.growth_arith
#print axioms ZetaGrowthEM3.zeta_growth_left_bound
#print axioms ZetaGrowthEM3.zeta_growth_left_rpow
#print axioms ZetaGrowthEM3.zeta_growth_left
-- ZeroAvoidingHeights
#print axioms ZeroAvoidingHeights.K7_nonneg
#print axioms ZeroAvoidingHeights.eight_le_denom
#print axioms ZeroAvoidingHeights.δ_pos
#print axioms ZeroAvoidingHeights.δ_le_eighth
#print axioms ZeroAvoidingHeights.card_mul_two_δ_lt_one
#print axioms ZeroAvoidingHeights.ncard_window_le
#print axioms ZeroAvoidingHeights.exists_height_avoiding_zeros
#print axioms ZeroAvoidingHeights.exists_seq_heights
#print axioms ZeroAvoidingHeights.heights_tendsto_atTop
-- LogDerivSegmentBound
#print axioms LogDerivSegmentBound.norm_logDeriv_le_of_norm_le_general
#print axioms LogDerivSegmentBound.norm_logDeriv_sub_sum_le_of_factorization_general
#print axioms LogDerivSegmentBound.exists_partialFraction_bound_of_finite_zeros
#print axioms LogDerivSegmentBound.abs_re_sub_lt_and_abs_im_sub_lt_of_mem_ball
#print axioms LogDerivSegmentBound.two_le_abs_im_of_mem_ball
#print axioms LogDerivSegmentBound.one_not_mem_closedBall
#print axioms LogDerivSegmentBound.isNontrivialZero_of_im_ne_zero
#print axioms LogDerivSegmentBound.norm_zeta_real_le
#print axioms LogDerivSegmentBound.norm_zeta_centre_ge
#print axioms LogDerivSegmentBound.norm_zeta_le_on_disc_of_growth
#print axioms LogDerivSegmentBound.exists_partialFraction_zeta_of_growth
#print axioms LogDerivSegmentBound.norm_logDeriv_zeta_le_of_growth
#print axioms LogDerivSegmentBound.two_thirds_le_log_two
#print axioms LogDerivSegmentBound.log_eleven_le_three
#print axioms LogDerivSegmentBound.logSize_concrete_le
#print axioms LogDerivSegmentBound.logSize_general_le
#print axioms LogDerivSegmentBound.norm_logDeriv_zeta_le_on_segment
#print axioms LogDerivSegmentBound.norm_logDeriv_zeta_le_on_full_segment_of_growth
#print axioms LogDerivSegmentBound.norm_logDeriv_zeta_le_on_line_three_halves
#print axioms LogDerivSegmentBound.norm_logDeriv_zeta_le_of_three_halves_le_re
-- TestFunctions
#print axioms TestFunctions.IsTestFn.continuous
#print axioms TestFunctions.IsTestFn.differentiable
#print axioms TestFunctions.IsTestFn.contDiff_deriv
#print axioms TestFunctions.IsTestFn.continuous_deriv
#print axioms TestFunctions.IsTestFn.differentiable_deriv
#print axioms TestFunctions.IsTestFn.continuous_deriv2
#print axioms TestFunctions.C₂_nonneg
#print axioms TestFunctions.hasDerivAt_exp_mul_ofReal
#print axioms TestFunctions.norm_exp_mul_ofReal
#print axioms TestFunctions.norm_exp_mul_ofReal_le
#print axioms TestFunctions.norm_integral_mul_exp_le
#print axioms TestFunctions.Gt_bound
#print axioms TestFunctions.hasDerivAt_Gt
#print axioms TestFunctions.Gt_differentiable
#print axioms TestFunctions.Gt_continuous
#print axioms TestFunctions.sq_mul_Gt_eq
#print axioms TestFunctions.Gt_decay
#print axioms TestFunctions.Gt_half_add_I_mul
#print axioms TestFunctions.Gt_at_ordinate
#print axioms TestFunctions.Gt_line_eq_fourier
#print axioms TestFunctions.Gt_half_line_eq_fourier
#print axioms TestFunctions.Gt_norm_le_div_one_add_sq
#print axioms TestFunctions.integrable_on_vertical_line
#print axioms TestFunctions.horizontal_vanishing

-- Segment bound for ζ'/ζ on -1/2 ≤ σ ≤ 3/2, unconditional (glue of LogDerivSegmentBound + ZetaGrowthEM3 + ZeroAvoidingHeights)
#print axioms SegmentBoundUnconditional.norm_logDeriv_zeta_le_on_full_segment
#print axioms SegmentBoundUnconditional.exists_heights_with_segment_bound

-- Fleet 6 (2026-09-12): left-line bound, prime side via Fourier inversion, zero-sum limit with multiplicities, horizontal vanishing, and THE EXPLICIT FORMULA (zero side)
-- LeftLineBound
#print axioms LeftLineBound.riemannZeta_ne_zero_of_re_eq_neg_half
#print axioms LeftLineBound.neg_half_add_mul_I_ne_one
#print axioms LeftLineBound.riemannZeta_left_line_ne_zero
#print axioms LeftLineBound.norm_logDeriv_zeta_left_line_logSize
#print axioms LeftLineBound.two_rpow_four
#print axioms LeftLineBound.log_const_le
#print axioms LeftLineBound.norm_logDeriv_zeta_left_line
#print axioms LeftLineBound.continuous_logDeriv_line
#print axioms LeftLineBound.continuous_logDeriv_left_line
#print axioms LeftLineBound.norm_logDeriv_zeta_left_line_all
#print axioms LeftLineBound.integrable_log_div_one_add_sq
#print axioms LeftLineBound.integrable_mul_of_log_bound
#print axioms LeftLineBound.integrable_logDeriv_mul_Gt_left
#print axioms LeftLineBound.integrable_logDeriv_mul_Gt_left'
#print axioms LeftLineBound.three_halves_add_mul_I_ne_one
#print axioms LeftLineBound.riemannZeta_right_line_ne_zero
#print axioms LeftLineBound.continuous_logDeriv_right_line
#print axioms LeftLineBound.integrable_logDeriv_mul_Gt_right
#print axioms LeftLineBound.integrable_logDeriv_mul_Gt_right'
-- PrimeSideLaplace
#print axioms PrimeSideLaplace.supp_Icc
#print axioms PrimeSideLaplace.psi_continuous
#print axioms PrimeSideLaplace.psi_eq_zero
#print axioms PrimeSideLaplace.psi_integrable
#print axioms PrimeSideLaplace.phi_continuous
#print axioms PrimeSideLaplace.phi_integrable
#print axioms PrimeSideLaplace.phi_eq_fourierInv_psi
#print axioms PrimeSideLaplace.phi_eq_fourierInv_psi'
#print axioms PrimeSideLaplace.fourier_psi_eq
#print axioms PrimeSideLaplace.fourier_psi_integrable
#print axioms PrimeSideLaplace.fourier_phi_eq_psi
#print axioms PrimeSideLaplace.psi_log
#print axioms PrimeSideLaplace.rpow_neg_three_halves_mul
#print axioms PrimeSideLaplace.coeff_mul_psi_eq
#print axioms PrimeSideLaplace.hasSum_rightLine_core
#print axioms PrimeSideLaplace.hasSum_rightLine
#print axioms PrimeSideLaplace.rightLine_eq_primeSide
#print axioms PrimeSideLaplace.summable_primeSide
#print axioms PrimeSideLaplace.rightLine_eq_primeSide_rpow
#print axioms PrimeSideLaplace.rightLine_eq_primeSide_t
#print axioms PrimeSideLaplace.Gt_indicator
#print axioms PrimeSideLaplace.continuous_indicator_of_testFn
#print axioms PrimeSideLaplace.indicator_supp
#print axioms PrimeSideLaplace.hasSum_rightLine_indicator
#print axioms PrimeSideLaplace.rightLine_eq_primeSide_indicator
-- ZeroSumLimit
#print axioms ZeroSumLimit.order_unique
#print axioms ZeroSumLimit.sum_order_mul_log_le_of_jensen
#print axioms ZeroSumLimit.sum_order_mul_log_le_of_jensen'
#print axioms ZeroSumLimit.sum_zetaOrder_near_height_le
#print axioms ZeroSumLimit.sum_zetaOrder_band_le
#print axioms ZeroSumLimit.dom_nonneg
#print axioms ZeroSumLimit.summable_dom
#print axioms ZeroSumLimit.log_div_sq_le_dom
#print axioms ZeroSumLimit.exists_bound_sum_zetaOrder_div_sq
#print axioms ZeroSumLimit.summable_inv_sq_im
#print axioms ZeroSumLimit.summable_norm_Gt
#print axioms ZeroSumLimit.summable_Gt
#print axioms ZeroSumLimit.mem_zeroFinset_three_halves
#print axioms ZeroSumLimit.sum_zeroFinset_eq
#print axioms ZeroSumLimit.tendsto_sum_zeroFinset
#print axioms ZeroSumLimit.hasSum_Gt
#print axioms ZeroSumLimit.fiber_canonical_eq
#print axioms ZeroSumLimit.multEnum_canonical
#print axioms ZeroSumLimit.zero_side_canonical
#print axioms ZeroSumLimit.exists_multEnum_nat
#print axioms ZeroSumLimit.zero_side_nat
-- HorizontalVanishingSeq
#print axioms HorizontalVanishingSeq.heights_spec
#print axioms HorizontalVanishingSeq.heights_ge
#print axioms HorizontalVanishingSeq.heights_le
#print axioms HorizontalVanishingSeq.heights_avoid
#print axioms HorizontalVanishingSeq.heights_avoid_neg
#print axioms HorizontalVanishingSeq.heights_pos
#print axioms HorizontalVanishingSeq.six_le_heights
#print axioms HorizontalVanishingSeq.heights_tendsto_atTop
#print axioms HorizontalVanishingSeq.one_le_log_heights
#print axioms HorizontalVanishingSeq.δ_pos
#print axioms HorizontalVanishingSeq.segment_bound_top
#print axioms HorizontalVanishingSeq.segment_bound_bot
#print axioms HorizontalVanishingSeq.Λ₀_nonneg
#print axioms HorizontalVanishingSeq.one_div_δ_le
#print axioms HorizontalVanishingSeq.segment_bound_log_sq_top
#print axioms HorizontalVanishingSeq.segment_bound_log_sq_bot
#print axioms HorizontalVanishingSeq.horizontal_vanishing_filter
#print axioms HorizontalVanishingSeq.horizontal_tendsto_zero_seq
#print axioms HorizontalVanishingSeq.horizontal_tendsto_zero_seq_neg
-- ExplicitFormulaZeroSide
#print axioms ExplicitFormulaZeroSide.right_pt
#print axioms ExplicitFormulaZeroSide.left_pt
#print axioms ExplicitFormulaZeroSide.bottom_pt
#print axioms ExplicitFormulaZeroSide.zeta_ne_zero_on_horizontal_edges
#print axioms ExplicitFormulaZeroSide.zeta_ne_zero_on_left_edge
#print axioms ExplicitFormulaZeroSide.boundary_nonvanishing
#print axioms ExplicitFormulaZeroSide.zeros_interior
#print axioms ExplicitFormulaZeroSide.contour_identity_at_height
#print axioms ExplicitFormulaZeroSide.neg_heights_tendsto_atBot
#print axioms ExplicitFormulaZeroSide.tendsto_right_truncated
#print axioms ExplicitFormulaZeroSide.tendsto_left_truncated
#print axioms ExplicitFormulaZeroSide.tendsto_top_edge
#print axioms ExplicitFormulaZeroSide.tendsto_bottom_edge
#print axioms ExplicitFormulaZeroSide.tendsto_zero_sum_truncated
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_raw
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side
#print axioms ExplicitFormulaZeroSide.hasSum_zero_side
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_canonical
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_nat
#print axioms ExplicitFormulaZeroSide.line_pt
#print axioms ExplicitFormulaZeroSide.rightLine_eq_two_pi_mul_integral_xi
#print axioms ExplicitFormulaZeroSide.integral_xi_eq_neg
#print axioms ExplicitFormulaZeroSide.rightLine_eq_neg_primeSide
#print axioms ExplicitFormulaZeroSide.rightLine_eq_neg_primeSide_indicator
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_primeSide
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_primeSide_indicator
#print axioms ExplicitFormulaZeroSide.explicit_formula_zero_side_primeSide_canonical
#print axioms TraceInterface.weilRHS_eq
#print axioms TraceInterface.zeros_realize
#print axioms TraceInterface.canonical_realizes
#print axioms TraceInterface.ordinate_eq_re_of_RH
#print axioms TraceInterface.realizes_of_RH
#print axioms TraceInterface.realizes_implies_RH_of_subset

-- ExpSumLowerBound
#print axioms ExpSumLowerBound.norm_exp_I_mul
#print axioms ExpSumLowerBound.integral_exp_mul_I_bound
#print axioms ExpSumLowerBound.integral_exp_zero
#print axioms ExpSumLowerBound.exists_large_of_nonempty
#print axioms RealSideBound.finite_small
#print axioms RealSideBound.exp_bound
#print axioms RealSideBound.exp_neg_sq_div_le
#print axioms RealSideBound.one_div_shift_le
#print axioms RealSideBound.exp_neg_sq_shift_le
#print axioms RealSideBound.gaussian_le_inv_sq
#print axioms RealSideBound.term_nonneg
#print axioms RealSideBound.summable_term
#print axioms RealSideBound.tsum_term_le
#print axioms RealSideBound.tsum_term_nonneg
#print axioms GaussianTest.bump_deriv_bound
#print axioms GaussianTest.cutoff_eq_one
#print axioms GaussianTest.cutoff_eq_zero
#print axioms GaussianTest.cutoff_contDiff
#print axioms GaussianTest.cutoff_deriv_bound
#print axioms GaussianTest.deriv_cutoff_eq_zero
#print axioms GaussianTest.gauss_contDiff
#print axioms GaussianTest.norm_gauss
#print axioms GaussianTest.hasDerivAt_gauss
#print axioms GaussianTest.hasDerivAt_gaussR
#print axioms GaussianTest.deriv2_gaussR
#print axioms GaussianTest.gaussR_contDiff
#print axioms GaussianTest.gaussR_support
#print axioms GaussianTest.gaussR_eq_of_small
#print axioms GaussianTest.gaussR_isTestFn
#print axioms GaussianTest.gaussHat_eq
#print axioms GaussianTest.norm_gaussHat
#print axioms GaussianTest.gaussHat_real
#print axioms GaussianTest.GtInf_gauss
#print axioms GaussianTest.Gt_bound_weighted
#print axioms GaussianTest.hfun_bound_weighted
#print axioms GaussianTest.majorant
#print axioms GaussianTest.norm_gaussR_le
#print axioms GaussianTest.norm_gaussR2_le
#print axioms GaussianTest.gaussR_weighted_uniform
#print axioms GaussianTest.gaussR_sup_uniform
#print axioms GaussianTest.tendsto_gaussR_integral
#print axioms GaussianTest.tendsto_gaussR_hfun
#print axioms GaussianTest.tendsto_gaussR_Gt
#print axioms GaussianTraceFormula.Gt_norm_le_weighted
#print axioms GaussianTraceFormula.weighted_integral_mono
#print axioms GaussianTraceFormula.continuous_deriv2_gaussR
#print axioms GaussianTraceFormula.exists_uniform_Gt_left_line
#print axioms GaussianTraceFormula.tendsto_leftLine
#print axioms GaussianTraceFormula.primeBound_nonneg
#print axioms GaussianTraceFormula.norm_natCast_cpow_neg_half_le
#print axioms GaussianTraceFormula.norm_primeTerm_le
#print axioms GaussianTraceFormula.summable_primeBound
#print axioms GaussianTraceFormula.tendsto_primeSum
#print axioms GaussianTraceFormula.tendsto_weilRHS
#print axioms GaussianTraceFormula.tendsto_hfun_sum
#print axioms GaussianTraceFormula.gaussian_formula_of_realizes
#print axioms GaussianTraceFormula.gaussian_formula_zeros
#print axioms GaussianTraceFormula.gaussian_formula_real
#print axioms GaussianTraceFormula.gaussian_trace_eq

-- OffLineDetection: Gaussian trace identity forces real ordinates (Fleet 7)
#print axioms OffLineDetection.t_re
#print axioms OffLineDetection.t_im
#print axioms OffLineDetection.abs_t_im_lt
#print axioms OffLineDetection.t_im_sq_lt
#print axioms OffLineDetection.Z_finite
#print axioms OffLineDetection.mem_Zfin
#print axioms OffLineDetection.summable_inv_one_add_sq_re
#print axioms OffLineDetection.neg_sq_eq
#print axioms OffLineDetection.gaussHat_polar
#print axioms OffLineDetection.norm_gaussHat_s
#print axioms OffLineDetection.w_nonneg
#print axioms OffLineDetection.summable_w
#print axioms OffLineDetection.far_exponent_le
#print axioms OffLineDetection.norm_gaussHat_far
#print axioms OffLineDetection.tail_bound
#print axioms OffLineDetection.real_side_bound
#print axioms OffLineDetection.exists_gap
#print axioms OffLineDetection.tsum_split
#print axioms OffLineDetection.key_estimate
#print axioms OffLineDetection.tendsto_bound
#print axioms OffLineDetection.ordinates_real
#print axioms OffLineDetection.RH_of_gaussian_trace
#print axioms TraceRealizationRH.real_trace_spectrum_implies_RH
#print axioms TraceRealizationRH.no_real_spectrum_of_not_RH
#print axioms TraceRealizationRH.summable_inv_one_add_sq_im
#print axioms TraceRealizationRH.RH_iff_exists_real_spectrum

-- Arithmetic/gamma bridge, including integrability and the independent target.
#print axioms GammaExplicitFormula.integrable_gamma
#print axioms GammaExplicitFormula.weilRHS_eq_gammaRHS
#print axioms GammaExplicitFormula.explicit_formula_gamma
#print axioms GammaExplicitFormula.explicit_formula_two_sided
#print axioms GammaExplicitFormula.realizes_gamma_iff
#print axioms GammaExplicitFormula.RH_iff_exists_gamma_spectrum

#print axioms FleetGammaDuplication.logDeriv_Gamma_two_mul


-- Conventional Gamma normalization and research limit interfaces.
#print axioms FleetGammaIdentification.digamma_eq_series
#print axioms FleetGammaGrowth.exists_strip_bound
#print axioms FleetKernelGrowth.exists_kernel_log_bound
#print axioms FleetStandardExplicitFormula.archimedean_eq_standard
#print axioms FleetStandardExplicitFormula.integrable_standard
#print axioms FleetStandardExplicitFormula.explicit_formula_standard
#print axioms FleetSeparatedExplicitFormula.explicit_formula_separated
#print axioms FleetStandardExplicitFormula.RH_iff_exists_standard_spectrum
#print axioms FleetFourierNormalization.integral_hfun
#print axioms FleetWeightedTrace.integral_tendsto_of_compact_tests_of_uniform_weight
#print axioms FleetSpectralTraceLimit.integral_eq_gammaRHS_of_residual_tendsto_zero
#print axioms FleetOffLineResponse.norm_symmetric_response_le

#print axioms FleetGlobalRealization.RH_of_arithmetic_approximation

#print axioms FleetAtomicLimit.measure_eq_unit_atoms_of_bounded_compact_configurations
#print axioms FleetBlockBound.form_lower_bound_of_schur

#print axioms FleetFiniteWindowEscape.exists_remote_paired_hfun_atoms
#print axioms FleetLocalAtomicLimit.exists_local_trace_representation

-- Later finite-spectrum closure and integral-tail additions (also focused audited).
#print axioms FleetLocalMeasureIdentity.exists_local_restricted_counting_measure
#print axioms FleetAtomicGluing.exists_countable_atomic_decomposition
#print axioms FleetWeightedAtomicClosure.exists_countable_spectrum
#print axioms FleetWeightedAtomicClosure.RH_of_finite_arithmetic_approximation
#print axioms FleetFiniteApproximation.RH_of_finite_trace_approximation
#print axioms FleetGaussianTail.gaussian_tail_integral

-- Finite-spectrum compactness and its exact arithmetic criterion.
#print axioms FleetOrderedAtoms.exists_ordered_permutation
#print axioms FleetOrderedAtoms.radius_lt_of_rank_ge
#print axioms FleetRealCompactification.continuous_extend
#print axioms FleetCompactSlots.exists_slot_subsequence
#print axioms FleetEncodedAtoms.trace_encode
#print axioms FleetPrefixMeasure.finiteOnCompacts
#print axioms FleetSlotLimit.compact_trace_tendsto
#print axioms FleetFiniteSpectrumCompactness.exists_vague_subsequence
#print axioms FleetFiniteSpectrumCompactness.RH_of_uniform_finite_approximation
#print axioms FleetFiniteTruncation.exists_inverse_quadratic_truncations
#print axioms FleetFiniteRealizationCriterion.RH_iff_finite_arithmetic_approximation
#print axioms FleetEscapeExample.weighted_integrals_not_tendsto_limit_mass

-- Joint dictionary approximation and fixed finite spans.
#print axioms FleetApproximationTransfer.finite_trace_difference_le
#print axioms FleetApproximationTransfer.residual_tendsto_of_dictionary
#print axioms FleetApproximationTransfer.RH_of_dictionary_approximation
#print axioms FleetLinearDictionary.residual_tendsto_linear_combination

-- Full-line arithmetic continuity and periodic approximation.
#print axioms FleetFullLineFourier.h_eq_fourier
#print axioms FleetFullLineFourier.h_deriv
#print axioms FleetFullLineFourier.norm_h_le
#print axioms FleetFullLineFourier.weighted_norm_h_le
#print axioms FleetFullLineFourier.h_eq_hfun
#print axioms FleetExponentialEnvelope.integral_envelope
#print axioms FleetExponentialEnvelope.integrable_envelope
#print axioms FleetExponentialEnvelope.integrable_of_bound
#print axioms FleetExponentialEnvelope.integral_norm_le
#print axioms FleetExponentialEnvelope.integrable_tilted
#print axioms FleetExponentialEnvelope.integral_norm_tilted_le
#print axioms FleetPrimeFunctionalBound.norm_term_le
#print axioms FleetPrimeFunctionalBound.summable_terms
#print axioms FleetPrimeFunctionalBound.norm_primeSum_le
#print axioms FleetPrimeFunctionalBound.primeSum_sub
#print axioms FleetPrimeFunctionalBound.norm_primeSum_sub_le
#print axioms FleetExponentialFourierBound.weighted_norm_h_le
#print axioms FleetExponentialFourierBound.imaginary_integrable
#print axioms FleetExponentialFourierBound.imaginary_norm_h_le
#print axioms FleetExponentialFourierBound.pole_norm_h_le
#print axioms FleetFullLineArithmetic.archimedean_eq_standard
#print axioms FleetFullLineArithmetic.rhs_eq_gammaRHS
#print axioms FleetArchimedeanFunctionalBound.integral_bound
#print axioms FleetArchimedeanFunctionalBound.exists_weight_integral_bound
#print axioms FleetArchimedeanFunctionalBound.exists_weight_log_bound
#print axioms FleetFullLineLinearity.h_sub
#print axioms FleetFullLineLinearity.integrable_real_integrand
#print axioms FleetFullLineLinearity.h_sub_real
#print axioms FleetFullLineLinearity.continuous_h_real
#print axioms FleetFullLineLinearity.archimedean_sub
#print axioms FleetCompactExponentialBound.exists_common_envelope
#print axioms FleetCompactExponentialBound.testFn_exists_common_envelope
#print axioms FleetArithmeticContinuity.exists_rhs_bound
#print axioms FleetArithmeticDifference.rhs_sub
#print axioms FleetArithmeticDifference.exists_difference_bound
#print axioms FleetExponentialDictionary.joint_approximation
#print axioms FleetExponentialDictionary.RH_of_exponential_dictionary
#print axioms FleetPeriodicApproximation.norm_le_period_mul_deriv_bound
#print axioms FleetPeriodicApproximation.norm_bounds_of_second_deriv
#print axioms FleetTrigPrimitive.doublePrimitive_second_deriv
#print axioms FleetTrigPrimitive.exists_periodic_second_primitive
#print axioms FleetTrigDensity.exists_finite_fourier_approx
#print axioms FleetTrigDensity.exists_zero_mean_fourier_approx

#print axioms FleetExponentialSpace.bound_zero
#print axioms FleetExponentialSpace.bound_add
#print axioms FleetExponentialSpace.bound_const_mul
#print axioms FleetExponentialSpace.bound_sum
#print axioms FleetGaussianEnvelopeTail.polynomial_gaussian_tendsto_cocompact
#print axioms FleetGaussianEnvelopeTail.exists_tail_bound
#print axioms FleetGaussianDictionaryMember.h_gauss_eq
#print axioms FleetGaussianDictionaryMember.exists_bound
#print axioms FleetPeriodicC2Density.second_derivative_mean_zero
#print axioms FleetPeriodicC2Density.exists_finite_polynomial_C2_approx

-- Complete fixed-width rational Gaussian density and sufficient criterion.
#print axioms FleetSmoothPeriodization.eventually_eq_finite_sum
#print axioms FleetSmoothPeriodization.contDiff_periodize
#print axioms FleetSmoothPeriodization.periodic_periodize
#print axioms FleetSmoothPeriodization.deriv_periodize
#print axioms FleetSmoothPeriodization.second_deriv_periodize
#print axioms FleetSmoothPeriodization.periodize_C2
#print axioms FleetPeriodizationSupport.unique_shift
#print axioms FleetPeriodizationSupport.locallyFinite_shifts
#print axioms FleetPeriodizationSupport.central_tsum_eq
#print axioms FleetPeriodizationSupport.norm_tsum_le
#print axioms FleetPeriodicReplacement.exists_periodic_replacement
#print axioms FleetGaussianMultiplier.exists_multiplier_bound
#print axioms FleetGaussianMultiplier.pointwise_polynomial_bound
#print axioms FleetGaussianPeriodizationTail.exists_gaussian_gluing_radius
#print axioms FleetDampedPeriodicApproximation.exists_damped_polynomial_approx
#print axioms FleetGaussianUntwist.smooth
#print axioms FleetGaussianUntwist.compact
#print axioms FleetGaussianUntwist.damp_untwist
#print axioms FleetGaussianUntwist.exists_uniform_bound
#print axioms FleetGaussianFiniteSpan.exists_bound
#print axioms FleetGaussianFiniteSpan.h_sum_real
#print axioms FleetGaussianFiniteSpan.damped_fourier_mode
#print axioms FleetGaussianFiniteSpan.damped_polynomial
#print axioms FleetArithmeticLinearSpan.rhs_const_mul
#print axioms FleetArithmeticLinearSpan.rhs_add
#print axioms FleetArithmeticLinearSpan.rhs_sum
#print axioms FleetGaussianDensity.exists_rational_gaussian_approx
#print axioms FleetGaussianCriterion.rhs_test
#print axioms FleetGaussianCriterion.h_test
#print axioms FleetGaussianCriterion.RH_of_rational_gaussian_residuals
#print axioms FleetGaussianCriterion.RH_of_normalized_gaussian_residuals
#print axioms FleetFiniteGaussianFeasibility.RH_of_finite_bank_feasibility
#print axioms FleetFiniteGaussianFeasibility.exists_exhausting_bank
#print axioms FleetRationalBanks.monotone_bank
#print axioms FleetRationalBanks.eventually_mem_bank
#print axioms FleetFiniteProbeCertificate.necessary_inequality
#print axioms FleetFiniteProbeCertificate.infeasible_of_certificate
#print axioms FleetFiniteProbeCertificate.infeasible_of_approximate_certificate

-- The concrete all-stage criterion retains uniform feasibility as a hypothesis.
#print axioms FleetRationalBankCriterion.RH_of_feasible_stages
#print axioms FleetRationalBankCriterion.RH_of_uniform_feasibility

-- Conditional enclosure transfer and exact rational-coordinate mass checks.
#print axioms FleetFiniteIntervalCertificate.feasible_of_scalar_enclosures
#print axioms FleetFiniteIntervalCertificate.norm_le_box
#print axioms FleetFiniteIntervalCertificate.feasible_of_rectangular_enclosures
#print axioms FleetFiniteIntervalCertificate.feasible_mono_stage
#print axioms FleetFiniteIntervalCertificate.weighted_mass_le_strip_pair
#print axioms FleetFiniteIntervalCertificate.fourPairs_mass_le_002
#print axioms FleetFiniteIntervalCertificate.fivePairs_mass_gt_002
#print axioms FleetFiniteIntervalCertificate.fivePairs_mass_le_005

-- Exact rational mass check for the external stage-100 candidate.
#print axioms FleetStage100Witness.mass_le_one_twentieth

-- Proved elementary enclosures, analytic truncation, and quadrature soundness.
#print axioms FleetElementaryIntervalCertificate.exp_small
#print axioms FleetElementaryIntervalCertificate.exp_double
#print axioms FleetElementaryIntervalCertificate.log_of_exp
#print axioms FleetElementaryIntervalCertificate.cos_small
#print axioms FleetElementaryIntervalCertificate.cos_double
#print axioms FleetElementaryNumericalInstances.exp_one_sixteenth
#print axioms FleetElementaryNumericalInstances.exp_neg_144
#print axioms FleetElementaryNumericalInstances.exp_log_two_lower
#print axioms FleetElementaryNumericalInstances.exp_log_two_upper
#print axioms FleetElementaryNumericalInstances.log_two
#print axioms FleetElementaryNumericalInstances.exp_neg_144_le
#print axioms FleetGaussianPrimeTailCertificate.six_le_log_of_ge_1000
#print axioms FleetGaussianPrimeTailCertificate.gaussian_log_le_inv_sixth
#print axioms FleetGaussianPrimeTailCertificate.norm_gaussian_prime_term_le_inv_fifth
#print axioms FleetGaussianPrimeTailCertificate.inv_fifth_le_cube_mul_sq
#print axioms FleetGaussianPrimeTailCertificate.summable_gaussian_prime_terms
#print axioms FleetGaussianPrimeTailCertificate.norm_gaussian_prime_tail_le
#print axioms FleetGaussianPrimeTailCertificate.primeSum_sub_partial_eq
#print axioms FleetGaussianPrimeTailCertificate.primeSum_truncation_le
#print axioms FleetGaussianPrimeTailCertificate.primeSum_truncation_1000_le
#print axioms FleetGaussianPrimeTailCertificate.reflect_gauss_one
#print axioms FleetGaussianPrimeTailCertificate.reflected_primeSum_truncation_1000_le
#print axioms FleetGaussianPrimeTailCertificate.two_primeSums_truncation_1000_le
#print axioms FleetDigammaIntervalCertificate.norm_psi_sub_psiApprox_le
#print axioms FleetDigammaIntervalCertificate.quarterPoint_re
#print axioms FleetDigammaIntervalCertificate.norm_quarterPoint_sub_one_le
#print axioms FleetDigammaIntervalCertificate.norm_quarter_psi_sub_psiApprox_le
#print axioms FleetDigammaIntervalCertificate.psiApprox_re
#print axioms FleetDigammaIntervalCertificate.abs_re_psi_sub_realPsiApprox_le
#print axioms FleetDigammaIntervalCertificate.re_psi_mem_finite_interval
#print axioms FleetDigammaIntervalCertificate.abs_euler_sub_eulerApprox_le
#print axioms FleetDigammaIntervalCertificate.abs_re_psi_sub_arithmeticPsiApprox_le
#print axioms FleetDigammaIntervalCertificate.re_psi_mem_arithmetic_interval
#print axioms FleetDigammaIntervalCertificate.abs_re_psi_quarter_le_five
#print axioms FleetDigammaIntervalCertificate.norm_psi_quarter_le
#print axioms FleetDigammaIntervalCertificate.abs_log_pi_le_three
#print axioms FleetDigammaIntervalCertificate.abs_weight_le
#print axioms FleetDigammaIntervalCertificate.abs_weight_sub_arithmeticWeightApprox_le
#print axioms FleetIntervalQuadratureCertificate.cell_integral_enclosure
#print axioms FleetIntervalQuadratureCertificate.partition_integral_enclosure
#print axioms FleetIntervalQuadratureCertificate.quadrature_error_le
#print axioms FleetIntervalQuadratureCertificate.midpoint_error_le
#print axioms FleetGaussianArchimedeanNormalization.integral_change_variables
#print axioms FleetGaussianArchimedeanNormalization.archimedean_gauss_one
#print axioms FleetArchimedeanTailCertificate.continuous_normIntegrand
#print axioms FleetArchimedeanTailCertificate.normIntegrand_nonneg
#print axioms FleetArchimedeanTailCertificate.translated_envelope
#print axioms FleetArchimedeanTailCertificate.translated_tail
#print axioms FleetArchimedeanTailCertificate.positive_tail
#print axioms FleetArchimedeanTailCertificate.normIntegrand_neg
#print axioms FleetArchimedeanTailCertificate.negative_tail
#print axioms FleetArchimedeanTailCertificate.two_sided_tail
#print axioms FleetArchimedeanTailCertificate.continuous_integrand
#print axioms FleetArchimedeanTailCertificate.norm_integrand
#print axioms FleetArchimedeanTailCertificate.integrable_normIntegrand
#print axioms FleetArchimedeanTailCertificate.integrable_integrand
#print axioms FleetArchimedeanTailCertificate.truncation_bound
#print axioms FleetArchimedeanTailCertificate.normalized_truncation_bound
#print axioms FleetArchimedeanTailCertificate.twice_oneSidedBound_twelve_le
#print axioms FleetArchimedeanTailCertificate.normalized_truncation_twelve_le
#print axioms FleetGaussianFiniteReduction.archimedean_sub_finite_le
#print axioms FleetGaussianFiniteReduction.rhs_sub_finiteRHS_le

-- Efficient, computable enclosures and derivative-based quadrature.
#print axioms FleetRationalInterval.point_contains
#print axioms FleetRationalInterval.add_contains
#print axioms FleetRationalInterval.neg_contains
#print axioms FleetRationalInterval.sub_contains
#print axioms FleetRationalInterval.square_contains
#print axioms FleetRationalInterval.mul_contains
#print axioms FleetRationalInterval.invPositive_contains
#print axioms FleetRationalInterval.roundDown_le
#print axioms FleetRationalInterval.le_roundUp
#print axioms FleetRationalInterval.rounded_contains
#print axioms FleetRationalInterval.expSeed_contains
#print axioms FleetRationalInterval.repeatedSquare_exp_contains
#print axioms FleetRationalInterval.expScaled_contains
#print axioms FleetRationalInterval.expAt_contains
#print axioms FleetRationalInterval.expInterval_contains
#print axioms FleetRationalInterval.enlarge
#print axioms FleetRationalInterval.logBisect_contains
#print axioms FleetRationalInterval.logAt_contains
#print axioms FleetRationalInterval.logInterval_contains
#print axioms FleetFastLogCertificate.odd_tail_bound
#print axioms FleetFastLogCertificate.reduced_parameter_bounds
#print axioms FleetFastLogCertificate.reduced_log_hasSum
#print axioms FleetFastLogCertificate.logPolynomial_error
#print axioms FleetFastLogCertificate.log_scale_pow_two
#print axioms FleetFastLogCertificate.logPolynomial_error_eight
#print axioms FleetFastLogCertificate.logPolynomialQ_cast
#print axioms FleetFastLogCertificate.logErrorQ_cast
#print axioms FleetFastLogCertificate.reducedLog_contains
#print axioms FleetFastLogCertificate.logTwoBox_contains
#print axioms FleetFastLogCertificate.logFast_contains
#print axioms FleetFastLogCertificate.logAtFast_contains
#print axioms FleetFastLogCertificate.logIntervalFast_contains
#print axioms FleetDigammaEfficientCertificate.asymptotic_step_bound
#print axioms FleetDigammaEfficientCertificate.two_inv_cube_le_sub_inv_sq
#print axioms FleetDigammaEfficientCertificate.center_increment_bound
#print axioms FleetDigammaEfficientCertificate.center_difference_bound
#print axioms FleetDigammaEfficientCertificate.arithmeticPsiApprox_diagonal
#print axioms FleetDigammaEfficientCertificate.tendsto_logSumCenter
#print axioms FleetDigammaEfficientCertificate.tendsto_asymptotic_sub_log_nat
#print axioms FleetDigammaEfficientCertificate.tendsto_center
#print axioms FleetDigammaEfficientCertificate.abs_re_psi_sub_center_le
#print axioms FleetDigammaEfficientCertificate.quarter_inv_re
#print axioms FleetDigammaEfficientCertificate.center_eq_efficientPsiApprox
#print axioms FleetDigammaEfficientCertificate.abs_re_psi_sub_efficientPsiApprox_le
#print axioms FleetDigammaEfficientCertificate.abs_weight_sub_efficientWeightApprox_le
#print axioms FleetDigammaPointCertificate.denominator_bounds
#print axioms FleetDigammaPointCertificate.rationalTermsBox_contains
#print axioms FleetDigammaPointCertificate.rationalTerms_cast
#print axioms FleetDigammaPointCertificate.psiApproxAt_contains
#print axioms FleetDigammaPointCertificate.psiAt_contains
#print axioms FleetDigammaPointCertificate.piBox_contains
#print axioms FleetDigammaPointCertificate.logPiBox_contains
#print axioms FleetDigammaPointCertificate.weightAt_contains
#print axioms FleetConcreteDigammaEnclosures.psi_quarter
#print axioms FleetConcreteDigammaEnclosures.psi_quarter_add_I
#print axioms FleetConcreteDigammaEnclosures.weight_one_hundred
#print axioms FleetEfficientArchimedeanCertificate.measurable_efficientIntegrand
#print axioms FleetEfficientArchimedeanCertificate.norm_integrand_sub_le
#print axioms FleetEfficientArchimedeanCertificate.integrable_integrand_sub
#print axioms FleetEfficientArchimedeanCertificate.integrable_efficientIntegrand
#print axioms FleetEfficientArchimedeanCertificate.normalized_replacement_bound
#print axioms FleetEfficientArchimedeanCertificate.normalized_replacement_thirty_two
#print axioms FleetArchimedeanPointCertificate.efficientWeightAt_contains
#print axioms FleetArchimedeanPointCertificate.integrandAt_contains
#print axioms FleetArchimedeanPointCertificate.sqrtPiBox_contains
#print axioms FleetArchimedeanPointCertificate.invSqrtPiBox_contains
#print axioms FleetArchimedeanPointCertificate.sumRangeAux_contains
#print axioms FleetArchimedeanPointCertificate.sumRange_contains
#print axioms FleetArchimedeanPointCertificate.sumPowerTwo_contains
#print axioms FleetGaussianFiniteClosedForm.exp_pair
#print axioms FleetGaussianFiniteClosedForm.pole_pair
#print axioms FleetGaussianFiniteClosedForm.nat_cpow_neg_half
#print axioms FleetGaussianFiniteClosedForm.gauss_pair
#print axioms FleetGaussianFiniteClosedForm.paired_prime_term
#print axioms FleetGaussianFiniteClosedForm.primeTermReal_zero
#print axioms FleetGaussianFiniteClosedForm.primeTermReal_one
#print axioms FleetGaussianFiniteClosedForm.paired_prime_term_zero
#print axioms FleetGaussianFiniteClosedForm.paired_prime_term_one
#print axioms FleetGaussianFiniteClosedForm.paired_partialSum
#print axioms FleetGaussianFiniteClosedForm.finiteRHS_eq_real
#print axioms FleetMidpointQuadrature.convex_tangent_le
#print axioms FleetMidpointQuadrature.taylor_upper_of_second_deriv_le
#print axioms FleetMidpointQuadrature.abs_taylor_remainder_le
#print axioms FleetMidpointQuadrature.integral_midpoint_linear
#print axioms FleetMidpointQuadrature.integral_midpoint_quadratic
#print axioms FleetMidpointQuadrature.midpoint_error_of_hasDerivAt
#print axioms FleetMidpointQuadrature.midpoint_error_le
#print axioms FleetMidpointQuadrature.partition_midpoint_error_le
#print axioms FleetMidpointQuadrature.uniform_midpoint_error_le
#print axioms FleetMidpointDerivativeGrid.uniform_midpoint_error_of_hasDerivAt

-- Actual integral enclosures from a fixed, justified numerical grid.
#print axioms FleetEfficientArchimedeanDerivatives.point_real_re
#print axioms FleetEfficientArchimedeanDerivatives.point_ne_zero
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_point
#print axioms FleetEfficientArchimedeanDerivatives.complexApprox_re
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_complexApprox
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_complexFirst
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_efficientPsiApprox
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_first
#print axioms FleetEfficientArchimedeanDerivatives.norm_point_inv_le
#print axioms FleetEfficientArchimedeanDerivatives.norm_point_inv_le_four
#print axioms FleetEfficientArchimedeanDerivatives.norm_point_inv_le_one
#print axioms FleetEfficientArchimedeanDerivatives.sum_recip_sq_le
#print axioms FleetEfficientArchimedeanDerivatives.sum_norm_inv_sq_le
#print axioms FleetEfficientArchimedeanDerivatives.sum_norm_inv_cube_le
#print axioms FleetEfficientArchimedeanDerivatives.abs_first_le
#print axioms FleetEfficientArchimedeanDerivatives.abs_second_le
#print axioms FleetEfficientArchimedeanDerivatives.norm_psi_le_forty_five
#print axioms FleetEfficientArchimedeanDerivatives.shiftedWeight_eq
#print axioms FleetEfficientArchimedeanDerivatives.abs_shiftedWeight_le
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_shiftedWeight
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_shiftedFirst
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_gaussian
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_integrand
#print axioms FleetEfficientArchimedeanDerivatives.hasDerivAt_integrandFirst
#print axioms FleetEfficientArchimedeanDerivatives.gaussian_le_one
#print axioms FleetEfficientArchimedeanDerivatives.gaussian_mul_sq_le_one
#print axioms FleetEfficientArchimedeanDerivatives.gaussian_mul_abs_le_two
#print axioms FleetEfficientArchimedeanDerivatives.abs_integrandSecond_le
#print axioms FleetEfficientArchimedeanDerivatives.continuous_integrand
#print axioms FleetEfficientMidpointCertificate.midpoint_error
#print axioms FleetEfficientMidpointCertificate.normalized_midpoint_error
#print axioms FleetEfficientMidpointCertificate.actual_normalized_midpoint_error
#print axioms FleetEfficientMidpointCertificate.actual_normalized_midpoint_error_stage100
#print axioms FleetEfficientMidpointCertificate.actual_normalized_midpoint_16384_le
#print axioms FleetArchimedeanNumericalCertificate.sample_bounds
#print axioms FleetArchimedeanNumericalCertificate.midpointBox_contains
#print axioms FleetArchimedeanNumericalCertificate.archimedeanAt_contains

-- Sharper integral enclosure with a smaller certified grid.
#print axioms FleetSharpMidpointCertificate.gaussian_mul_abs_le_half
#print axioms FleetSharpMidpointCertificate.gaussian_mul_curvature_le_two
#print axioms FleetSharpMidpointCertificate.sum_recip_thirty_two_le_eight
#print axioms FleetSharpMidpointCertificate.psi_rational_sum_le_eight
#print axioms FleetSharpMidpointCertificate.abs_efficientWeight_thirty_two_le
#print axioms FleetSharpMidpointCertificate.abs_shiftedWeight_thirty_two_le
#print axioms FleetSharpMidpointCertificate.abs_integrandSecond_thirty_two_le_230
#print axioms FleetSharpMidpointCertificate.abs_integrandSecond_thirty_two_le_256
#print axioms FleetSharpMidpointCertificate.midpoint_error_sharp
#print axioms FleetSharpMidpointCertificate.normalized_midpoint_error_sharp
#print axioms FleetSharpMidpointCertificate.actual_normalized_midpoint_error_sharp
#print axioms FleetSharpMidpointCertificate.actual_normalized_midpoint_4096_le

-- Gaussian dual bounds, with residual uncertainty and no strong-duality premise.
#print axioms FleetGaussianDualCertificate.weak_duality_config
#print axioms FleetGaussianDualCertificate.weak_duality
#print axioms FleetGaussianDualCertificate.mass_lower_bound
#print axioms FleetGaussianDualCertificate.weak_duality_approximate_config
#print axioms FleetGaussianDualCertificate.weak_duality_approximate
#print axioms FleetGaussianDualCertificate.mass_lower_bound_approximate
#print axioms FleetGaussianDualCertificate.exists_eventually_infeasible_of_not_RH
#print axioms FleetGaussianDualCertificate.eventually_mass_gt_of_not_RH
#print axioms FleetGaussianThreeProbe.detector_eq_cosh
#print axioms FleetGaussianThreeProbe.detector_real_nonpos
#print axioms FleetGaussianThreeProbe.detector_displaced_pair
#print axioms FleetGaussianThreeProbe.detector_shift_real_neg
#print axioms FleetGaussianThreeProbe.exists_repeated_real_background
#print axioms FleetGaussianThreeProbe.three_residual_inequality
#print axioms FleetGaussianThreeProbe.stage_inequality
#print axioms FleetGaussianThreeProbe.infeasible_of_stage_gap
#print axioms FleetGaussianThreeProbe.background_margin_impossible

-- FleetThreeCentreInequality: finite-stage three-centre infeasibility certificate (2026-10-01)
#print axioms FleetThreeCentreInequality.three_centre_of_feasible
#print axioms FleetThreeCentreInequality.infeasible_of_three_centre_violation
#print axioms FleetThreeCentreInequality.three_point
#print axioms FleetThreeCentreInequality.probe_real

-- StripWidthDependency: the strip half-width as a free parameter (2026-11-06)
#print axioms StripWidthDependency.stripHalfWidth_half
#print axioms StripWidthDependency.stripHalfWidth_iff_re_bounds
#print axioms StripWidthDependency.stripHalfWidth_of_zeroFree
#print axioms StripWidthDependency.stripHalfWidth_of_ordinates_real
#print axioms StripWidthDependency.far_exponent_le_delta
#print axioms StripWidthDependency.norm_gaussHat_far_delta
#print axioms StripWidthDependency.far_bound_delta_half
#print axioms StripWidthDependency.farDecayRate_antitone
#print axioms StripWidthDependency.farDecayRate_five_twelfths

-- FleetDualInequality: feasible stage => prime-side inequality for every finite Gaussian weighting (2026-11-09)
#print axioms FleetDualInequality.dual_of_feasible
#print axioms FleetDualInequality.infeasible_of_dual_violation
#print axioms FleetDualInequality.uniform_dual_inequality
#print axioms FleetDualInequality.uniform_positivity

-- FleetDualConverse: prime-side inequality <=> weighted stage feasibility, via Hahn-Banach (2026-11-09)
#print axioms FleetDualConverse.weightedFeasible_of_dualIneq
#print axioms FleetDualConverse.dualIneq_of_weightedFeasible
#print axioms FleetDualConverse.weightedFeasible_iff_dualIneq

-- FleetTraceBoundRH: RH <=> Gaussian zero trace is O(b^{-1/2}) at every centre (2026-11-09)
#print axioms FleetTraceBoundRH.RH_of_zero_trace_bound
#print axioms FleetTraceBoundRH.zero_trace_bound_of_RH
#print axioms FleetTraceBoundRH.RH_iff_zero_trace_bound
#print axioms FleetTraceBoundRH.RH_iff_zero_trace_bound'
-- FleetArithmeticBoundRH: RH <=> arithmetic side (pole - primes - archimedean) is O(b^{-1/2}) at every centre (2026-11-10)
#print axioms FleetArithmeticBoundRH.zero_trace_eq_arithmetic
#print axioms FleetArithmeticBoundRH.RH_iff_arithmetic_bound
-- FleetPrimePoleBoundRH: rhs(gauss) = contour form; archimedean is O(b^{-1/2}); RH <=> pole-minus-primes is O(b^{-1/2}) (2026-11-10)
#print axioms FleetPrimePoleBoundRH.rhs_gauss_eq
#print axioms FleetPrimePoleBoundRH.zero_trace_eq_rhs
#print axioms FleetPrimePoleBoundRH.norm_archimedean_le
#print axioms FleetPrimePoleBoundRH.RH_iff_pole_prime_bound
-- FleetPrimeSideConsequences: pure prime sum for |alpha| >= 1/2; verified-range bound; RH <=> uniform feasibility (2026-11-10)
#print axioms FleetPrimeSideConsequences.norm_poleTerm_le_of_half_le_abs
#print axioms FleetPrimeSideConsequences.poleMinusPrimes_bound_iff_primeSumSym_bound
#print axioms FleetPrimeSideConsequences.zero_trace_bound_of_verified
#print axioms FleetPrimeSideConsequences.pole_prime_bound_of_verified
#print axioms FleetPrimeSideConsequences.uniformFeasibility_of_RH
#print axioms FleetPrimeSideConsequences.RH_iff_uniformFeasibility
-- FleetPrimeOnlyRH: proper prime powers cost O(b^{-1/2}); RH <=> the criterion over primes only (2026-11-10)
#print axioms FleetPrimeOnlyRH.sum_thetaW_le
#print axioms FleetPrimeOnlyRH.abel_le
#print axioms FleetPrimeOnlyRH.primes_weighted
#print axioms FleetPrimeOnlyRH.tsum_rW_le
#print axioms FleetPrimeOnlyRH.norm_primeSumSym_sub_primeOnlySym_le
#print axioms FleetPrimeOnlyRH.RH_iff_primeOnly_bound
#print axioms FleetPrimeOnlyRH.pole_prime_bound_iff_primeOnly_bound
#print axioms FleetPrimeOnlyRH.RH_iff_primeSumSym_bound_of_verified
#print axioms FleetPrimeOnlyRH.RH_iff_primeOnlySym_bound_of_verified
-- BoundaryTripleReal: Green's identity makes eigenvalues under a real boundary form real (2026-11-10)
#print axioms BoundaryTripleReal.im_eigenvalue_mul_normSq
#print axioms BoundaryTripleReal.im_eigenvalue_zero_of_boundaryTriple
#print axioms BoundaryTripleReal.boundary_form_real_of_real_condition
-- FleetLowZeroFree: zeta has no zeros with 0<Re s<1, |Im s|<=3/2; VerifiedTo (3/2) proved; RH <=> pure prime sum bound at |alpha|>=1/2 (2026-11-10)
#print axioms FleetLowZeroFree.zeta_ne_zero_low
#print axioms FleetLowZeroFree.verifiedTo_three_halves
#print axioms FleetLowZeroFree.RH_iff_primeSumSym_bound
#print axioms FleetLowZeroFree.RH_iff_primeOnlySym_bound
-- FleetMoebiusSmoothDecomposition: S_b = sum_m mu(m) m^{-1/2} I_b(alpha, log m), I_b smooth over all integers (2026-11-10)
#print axioms FleetMoebiusSmoothDecomposition.primeSumSym_eq_moebius_double
#print axioms FleetMoebiusSmoothDecomposition.primeSumSym_eq_moebius_smooth
-- FleetPrimeTarget: cosine form of the prime sum; PrimeTarget named; RH <=> PrimeTarget (2026-11-10)
#print axioms FleetPrimeTarget.primeOnlySym_eq_real
#print axioms FleetPrimeTarget.RH_iff_PrimeTarget
-- FleetSquareBank: RH => every square Gaussian-bank Hankel form on the arithmetic side is >= 0 (2026-11-10)
#print axioms FleetSquareBank.bank_eq_square
#print axioms FleetSquareBank.bank_form_nonneg_of_RH
#print axioms FleetSquareBank.not_RH_of_bank_form_neg
-- FleetExponentLadder: bound sqrt(pi/b) C e^{c/b} => all zeros in |Re rho - 1/2| <= 2 sqrt c (2026-11-10)
#print axioms FleetExponentLadder.zeros_in_strip_of_exp_bound
#print axioms FleetExponentLadder.zeros_in_strip_of_pole_prime_exp_bound
-- FleetHeatPositivityRH: RH <=> Re R_b(alpha) >= 0 for all b in (0,1], alpha (zero side and arithmetic side) (2026-11-10)
#print axioms FleetHeatPositivityRH.ordinates_real_of_heat_positivity
#print axioms FleetHeatPositivityRH.RH_of_heat_positivity
#print axioms FleetHeatPositivityRH.RH_iff_heat_positivity
#print axioms FleetHeatPositivityRH.RH_iff_rhs_positivity
-- FleetPositivityDefect: Re R_b >= -sqrt(pi/b) C e^{c/b} (or the same for rhs) => all zeros in |Re rho - 1/2| <= 2 sqrt c (2026-11-10)
#print axioms FleetPositivityDefect.im_sq_le_of_defect
#print axioms FleetPositivityDefect.zeros_in_strip_of_defect
#print axioms FleetPositivityDefect.zeros_in_strip_of_rhs_defect
-- FleetTwoPointConvexity: RH <=> R_b(a+h)^2 <= e^{h^2/2b} R_b(a) R_b(a+2h) for all b, a, h (given one positive value per b) (2026-11-10)
#print axioms FleetTwoPointConvexity.twoPoint_of_RH
#print axioms FleetTwoPointConvexity.RH_of_twoPoint
#print axioms FleetTwoPointConvexity.RH_iff_twoPoint
-- FleetWeilNonArch: DeepMind formal-conjectures weilNonArchimedean summed over primes = von Mangoldt sum (2026-11-10)
#print axioms FleetWeilNonArch.sum_weilNonArchimedean_eq
-- FleetSinhIdentity: e^{h^2/2b}R(q-h)R(q+h) - R(q)^2 = 2 sum_ij w_i w_j g_i g_j sinh^2(h(gi-gj)/4b); nonneg weights => two-point log-convexity (2026-11-10)
#print axioms FleetSinhIdentity.sinh_sq_identity
#print axioms FleetSinhIdentity.two_point_of_nonneg
-- FleetDivisorCertificate: sum_{d|n} Lambda = log n turns multipliers U into an exact certificate; coverage at prime powers => prime sum <= budget; bank (matrix PSD) version (2026-11-10)
#print axioms FleetDivisorCertificate.swap
#print axioms FleetDivisorCertificate.certificate_identity
#print axioms FleetDivisorCertificate.prime_sum_le_budget
#print axioms FleetDivisorCertificate.lower_bound_of_coverage
#print axioms FleetDivisorCertificate.bank_posSemidef_of_certificate
#print axioms FleetDivisorCertificate.excess_ge_floor
-- FleetMultiplierFreedom: budget depends only on prime-power coverage; coprime moves d_ab-d_a-d_b free; telescoping u0 exact; composite coordinates determine exact-coverage multipliers (2026-11-10)
#print axioms FleetMultiplierFreedom.budget_eq_of_coverage_eq
#print axioms FleetMultiplierFreedom.coverage_coprime_move
#print axioms FleetMultiplierFreedom.budget_coprime_move
#print axioms FleetMultiplierFreedom.coverage_telescope
#print axioms FleetMultiplierFreedom.eq_of_coverage_eq
-- FleetMoebiusTail: finite Moebius form of the prime sum; mollified budget = truncation; gap = Moebius tail; prime-free bound via Lambda <= log (2026-11-10)
#print axioms FleetMoebiusTail.budget_eq
#print axioms FleetMoebiusTail.prime_sum_eq_moebius
#print axioms FleetMoebiusTail.prime_sum_sub_budget
#print axioms FleetMoebiusTail.prime_sum_le_free_bound
-- FleetMoebiusTailBound: Moebius tail beyond log M >= 1.1/b is <= 2 exp(-0.6375/b), absolute, unconditional; mollified budget = prime sum to that accuracy (2026-11-10)
#print axioms FleetMoebiusTailBound.moebius_tail_bound
#print axioms FleetMoebiusTailBound.prime_sum_near_budget

-- Infinite-inner-sum Gaussian Moebius tail, exact real cutoff, and right-sided Big-O.
#print axioms FleetMollifierTail.kernel_cubic
#print axioms FleetMollifierTail.inner_summable_and_bound
#print axioms FleetMollifierTail.moebius_finite_tail_bound
#print axioms FleetMollifierTail.windowTail_exponential
#print axioms FleetMollifierTail.windowTail_normalized
#print axioms FleetMollifierTail.windowTail_isBigO
#print axioms FleetMollifierTail.kernel_eq_rpow
-- FleetFiniteHeadRH: m^{-1/2} Ismooth(log m) = FleetMollifierTail.inner m; S_b = finite Moebius head (m <= e^{1.1/b}) + O(e^{-0.6375/b}); RH <=> head bound (2026-11-11)
#print axioms FleetFiniteHeadRH.ismooth_eq_inner
#print axioms FleetFiniteHeadRH.primeSumSym_eq_inner
#print axioms FleetFiniteHeadRH.primeSumSym_sub_head
#print axioms FleetFiniteHeadRH.RH_iff_head_bound
-- FleetHeadContour: head = Phi'(1) + (1/2pi) int LG(-it) M_M(1/2+it) (-zeta'(1/2+it)) dt (exact contour identity); window mean square of M_{cut b} = O(b^{-k}) => RH (conditional) (2026-11-11)
#print axioms FleetHeadContour.differentiable_zetaReg
#print axioms FleetHeadContour.deriv_riemannZeta_eq
#print axioms FleetHeadContour.norm_zetaReg_le
#print axioms FleetHeadContour.norm_deriv_zetaReg_le
#print axioms FleetHeadContour.norm_deriv_zeta_le
#print axioms FleetHeadContour.neg_deriv_zeta_eq_tsum
#print axioms FleetHeadContour.kernel_eq_integral
#print axioms FleetHeadContour.norm_LGw_le
#print axioms FleetHeadContour.integrable_of_gauss_bound
#print axioms FleetHeadContour.inner_eq_line_integral
#print axioms FleetHeadContour.head_eq_line_integral
#print axioms FleetHeadContour.rect_shift
#print axioms FleetHeadContour.line_shift
#print axioms FleetHeadContour.head_eq_critical_line
#print axioms FleetHeadContour.head_exp_ladder
#print axioms FleetHeadContour.zeta_window
#print axioms FleetHeadContour.norm_deriv_Phi_one_le
#print axioms FleetHeadContour.head_le_of_window
#print axioms FleetHeadContour.RH_of_window_meanSquare
#print axioms FleetHeadContour.windowSubexp_of_meanSquare
#print axioms FleetHeadContour.head_le_of_window_at
#print axioms FleetHeadContour.RH_of_window_subexp
-- FleetHeadContourStrip: Cauchy-Schwarz head bound; window rate C e^{c/b} at every |alpha| >= 1/2 => |Re rho - 1/2| <= sqrt(2c) (2026-11-11)
#print axioms FleetHeadContour.le_sqrt_mul_of_forall
#print axioms FleetHeadContour.head_le_of_window_at_cs
#print axioms FleetHeadContour.strip_of_head_exp
#print axioms FleetHeadContour.zeros_in_strip_of_window_rate
-- QuasiRHProved: QuasiRHWiring.QuasiRH (zeta(s) != 0 for Re s > 7/8) proved by OpenAI's Lean theorem, vendored under OAI/ (github.com/openai/math @ 4eaee87, Apache-2.0); OAI closure (2,943 files) audited via its two exported theorems (2026-11-11)
#print axioms OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
#print axioms OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re
-- FleetHeadContourConverse: unconditional window rate 11/10; Moebius-sum bound => window rate (11/5)(theta-1/2)+eps; strip delta + Landau transfer => rate (11/5)delta+eps; D^2/2 <= optimal rate (2026-11-11)
#print axioms FleetHeadContour.abs_re_sub_half_lt
#print axioms FleetHeadContour.bddAbove_dev
#print axioms FleetHeadContour.le_zeroDev
#print axioms FleetHeadContour.zeroDev_nonneg
#print axioms FleetHeadContour.zeroDev_le_iff
#print axioms FleetHeadContour.zeroDev_le_half
#print axioms FleetHeadContour.RH_iff_zeroDev_eq_zero
#print axioms FleetHeadContour.windowRate_mono
#print axioms FleetHeadContour.zeroDev_le_of_windowRate
#print axioms FleetHeadContour.windowSubexp_iff_forall_windowRate
#print axioms FleetHeadContour.two_sqrt_step
#print axioms FleetHeadContour.norm_Mpoly_half_le
#print axioms FleetHeadContour.headWindow_le_unconditional
#print axioms FleetHeadContour.windowRate_eleven_tenths
#print axioms FleetHeadContour.rateSet_nonempty
#print axioms FleetHeadContour.rateSet_bddBelow
#print axioms FleetHeadContour.windowRateInf_le_of_windowRate
#print axioms FleetHeadContour.windowRateInf_le_eleven_tenths
#print axioms FleetHeadContour.windowRateInf_nonneg
#print axioms FleetHeadContour.windowRate_of_windowRateInf_lt
#print axioms FleetHeadContour.zeroDev_sq_half_le_windowRateInf
#print axioms FleetHeadContour.windowSubexp_iff_windowRateInf_eq_zero
#print axioms FleetHeadContour.RH_of_windowRateInf_eq_zero
#print axioms FleetHeadContour.abel_range
#print axioms FleetHeadContour.norm_cpow_succ_sub_le
#print axioms FleetHeadContour.norm_Mpoly_half_le_of_moebius
#print axioms FleetHeadContour.poly_gauss_le
#print axioms FleetHeadContour.headWindow_le_of_moebius
#print axioms FleetHeadContour.windowRate_of_moebiusSumBound
#print axioms FleetHeadContour.windowRateInf_le_of_moebiusSumBound
#print axioms FleetHeadContour.windowSubexp_of_moebiusSumBound_half
#print axioms FleetHeadContour.windowRate_of_strip
#print axioms FleetHeadContour.windowRateInf_le_of_strip
#print axioms FleetHeadContour.RH_iff_windowSubexp
#print axioms FleetHeadContour.stripBound_of_quasiRH
#print axioms FleetHeadContour.windowRate_of_quasiRH
#print axioms FleetHeadContour.not_windowRate_of_lt
#print axioms FleetHeadContour.not_windowRate_sub
#print axioms FleetHeadContour.windowRateInf_bounds
-- FleetStripAttempt: Gaussian mean-value inequality for M_N; alpha-average of narrow windows = wide window; window rate 0 on alpha-average over widths B >= N^2 log 4N; squaring identity mu = 2 mu_N - 1*mu_N*mu_N on n <= N^2 (2026-11-11)
#print axioms FleetStripAttempt.sum_rsqrt_le
#print axioms FleetStripAttempt.term_eq
#print axioms FleetStripAttempt.conj_term
#print axioms FleetStripAttempt.Mpoly_half_eq
#print axioms FleetStripAttempt.normSq_Mpoly_half
#print axioms FleetStripAttempt.gauss_ofReal
#print axioms FleetStripAttempt.norm_gauss_fourier
#print axioms FleetStripAttempt.integrable_gauss_fourier
#print axioms FleetStripAttempt.Wg_le_double_sum
#print axioms FleetStripAttempt.abs_v_le
#print axioms FleetStripAttempt.sum_abs_v_le
#print axioms FleetStripAttempt.sum_sq_v_le
#print axioms FleetStripAttempt.log_gap
#print axioms FleetStripAttempt.sq_log_gap
#print axioms FleetStripAttempt.Wg_le_wide
#print axioms FleetStripAttempt.gauss_conv
#print axioms FleetStripAttempt.continuous_normSq_Mpoly
#print axioms FleetStripAttempt.normSq_Mpoly_le
#print axioms FleetStripAttempt.avg_Wg
#print axioms FleetStripAttempt.avg_window_le
#print axioms FleetStripAttempt.window_rate_zero_on_average
#print axioms FleetStripAttempt.muT_apply
#print axioms FleetStripAttempt.one_sub_zeta_muT_apply
#print axioms FleetStripAttempt.sq_one_sub_zeta_muT_apply
#print axioms FleetStripAttempt.moebius_eq_of_le_sq
#print axioms FleetStripAttempt.Mpoly_sq_eq
-- FleetSraSmoothing: Sra (2026) smoothing dictionary; strip Poisson kernel termwise positivity; sech-averaged Gaussian zero trace Re >= 0 unconditionally; window rate c <-> h^2/2; Freitas terms in unit disk (2026-11-11)
#print axioms FleetSraSmoothing.gaussHat_eq_sraGauss
#print axioms FleetSraSmoothing.norm_sraGauss_shift
#print axioms FleetSraSmoothing.norm_sraGauss_edge
#print axioms FleetSraSmoothing.re_sraGauss_shift
#print axioms FleetSraSmoothing.exists_re_sraGauss_neg
#print axioms FleetSraSmoothing.cosh_add_mul_I
#print axioms FleetSraSmoothing.normSq_cosh_add_mul_I
#print axioms FleetSraSmoothing.sechKernel_arg
#print axioms FleetSraSmoothing.re_sechKernel_shift
#print axioms FleetSraSmoothing.re_sechKernel_shift_pos
#print axioms FleetSraSmoothing.norm_sechKernel_shift_le
#print axioms FleetSraSmoothing.sub_ordinate_eq
#print axioms FleetSraSmoothing.abs_displacement_lt
#print axioms FleetSraSmoothing.sechKernel_zero_term_pos
#print axioms FleetSraSmoothing.sraGauss_ofReal
#print axioms FleetSraSmoothing.sechKernel_shift_sub
#print axioms FleetSraSmoothing.continuous_sechKernel_line
#print axioms FleetSraSmoothing.integrable_sechGauss_integrand
#print axioms FleetSraSmoothing.re_sechGauss_pos
#print axioms FleetSraSmoothing.sechGauss_zero_term_pos
#print axioms FleetSraSmoothing.sqrt_two_mul_half_sq
#print axioms FleetSraSmoothing.sqrt_two_mul_one_eighth
#print axioms FleetSraSmoothing.sqrt_two_mul_pi_sq_div_288
#print axioms FleetSraSmoothing.zeros_in_strip_of_window_rate_pi_sq_div_288
#print axioms FleetSraSmoothing.norm_div_sub_le_one_iff
#print axioms FleetSraSmoothing.freitas_terms_le_one_of_window_rate
#print axioms FleetSraSmoothing.gaussHat_eq_heat
#print axioms FleetSraSmoothing.zeroTrace_zero_eq_heat
#print axioms FleetSraSmoothing.integral_line_shift
#print axioms FleetSraSmoothing.cos_pi_le_of_abs_le
#print axioms FleetSraSmoothing.cos_pi_pos
#print axioms FleetSraSmoothing.norm_sechKernel_half_le
#print axioms FleetSraSmoothing.norm_sraGauss_ofReal
#print axioms FleetSraSmoothing.integrable_norm_sraGauss
#print axioms FleetSraSmoothing.norm_sraGauss_shift_le
#print axioms FleetSraSmoothing.tendsto_norm_sraGauss
#print axioms FleetSraSmoothing.integral_sech_gaussHat
#print axioms FleetSraSmoothing.re_integral_sech_gaussHat_pos
#print axioms FleetSraSmoothing.exp_abs_le_two_cosh
#print axioms FleetSraSmoothing.norm_sechKernel_half_real
#print axioms FleetSraSmoothing.norm_gaussHat_le_strip
#print axioms FleetSraSmoothing.exponent_ineq
#print axioms FleetSraSmoothing.integrand_bound
#print axioms FleetSraSmoothing.integrable_gauss_shift
#print axioms FleetSraSmoothing.integral_gauss_shift
#print axioms FleetSraSmoothing.continuous_sech_gaussHat
#print axioms FleetSraSmoothing.hasSum_sech_zeroTrace
#print axioms FleetSraSmoothing.re_sech_zeroTrace_nonneg
#print axioms FleetSraSmoothing.re_sech_zeroTrace_pos

-- FleetLandauTransferZeta/Perron, FleetLandauTransfer: zero-free half-plane Re s > 1/2+delta => 1/zeta << |t|^eta (Littlewood, three circles); Perron via Mellin inversion + contour shift; LandauTransfer delta proved for 0 <= delta < 1/2; strip/RH/QuasiRH window corollaries without the transfer hypothesis (2026-11-11)
#print axioms FleetLandauTransfer.three_circles
#print axioms FleetLandauTransfer.hasSum_inv_sq_from_two
#print axioms FleetLandauTransfer.pi_sq_div_six_sub_one_lt
#print axioms FleetLandauTransfer.zeta_sub_one_norm_le
#print axioms FleetLandauTransfer.zeta_norm_le_two
#print axioms FleetLandauTransfer.zeta_norm_ge_third
#print axioms FleetLandauTransfer.zeta_re_pos
#print axioms FleetLandauTransfer.log_zeta_norm_le
#print axioms FleetLandauTransfer.zeta_norm_le_poly
#print axioms FleetLandauTransfer.exists_log_ball
#print axioms FleetLandauTransfer.log_ball_eq_log
#print axioms FleetLandauTransfer.rpow_le_mul_add
#print axioms FleetLandauTransfer.thetaD_mem
#print axioms FleetLandauTransfer.littlewood_aux
#print axioms FleetLandauTransfer.littlewood_bound
#print axioms FleetLandauTransfer.sub_one_mul_zeta
#print axioms FleetLandauTransfer.invZeta_of_ne
#print axioms FleetLandauTransfer.invZeta_differentiableAt
#print axioms FleetLandauTransfer.invZeta_eq_LSeries
#print axioms FleetLandauTransfer.invZeta_differentiableAt_of_zeroFree
#print axioms FleetLandauTransfer.invZeta_bound
#print axioms FleetLandauTransfer.continuous_cesaro
#print axioms FleetLandauTransfer.cesaro_eq_indicator
#print axioms FleetLandauTransfer.ne_zero_of_re_pos
#print axioms FleetLandauTransfer.add_one_ne_zero_of_re_pos
#print axioms FleetLandauTransfer.hasMellin_cesaro
#print axioms FleetLandauTransfer.one_add_abs_im_le_norm
#print axioms FleetLandauTransfer.one_add_abs_im_le_norm_add_one
#print axioms FleetLandauTransfer.norm_pk_le
#print axioms FleetLandauTransfer.norm_pk
#print axioms FleetLandauTransfer.pk_div
#print axioms FleetLandauTransfer.pk_differentiableAt
#print axioms FleetLandauTransfer.continuous_pk_line
#print axioms FleetLandauTransfer.integrable_pk_line
#print axioms FleetLandauTransfer.integral_pk
#print axioms FleetLandauTransfer.cesaro_div
#print axioms FleetLandauTransfer.perron_general
#print axioms FleetLandauTransfer.norm_pk_mul_le
#print axioms FleetLandauTransfer.integrable_pk_mul_line
#print axioms FleetLandauTransfer.vertical_shift
#print axioms FleetLandauTransfer.norm_mul_cpow_sub_le
#print axioms FleetLandauTransfer.perron_mul_sub_eq
#print axioms FleetLandauTransfer.le_interp_of_le_two
#print axioms FleetLandauTransfer.kernel_bound
#print axioms FleetLandauTransfer.two_pi_Ssum
#print axioms FleetLandauTransfer.line_continuous
#print axioms FleetLandauTransfer.line_bound
#print axioms FleetLandauTransfer.Ssum_diff_bound
#print axioms FleetLandauTransfer.Ssum_diff
#print axioms FleetLandauTransfer.partial_sum_bound
#print axioms FleetHeadContour.zeta_ne_zero_of_stripBound
#print axioms FleetHeadContour.landauTransfer
#print axioms FleetHeadContour.windowRate_of_strip'
#print axioms FleetHeadContour.RH_iff_windowSubexp'
#print axioms FleetHeadContour.windowRate_of_quasiRH'
-- FleetDaneshCriterion: Danesh (arXiv:2611.10726) two-interval criterion; RH <=> Cauchy-Schwarz on narrow separated pairs; allowance e^{eta L} => |Re rho - 1/2| <= eta (2026-11-11)
#print axioms FleetDaneshCriterion.integrableOn_pow_mul_exp_neg
#print axioms FleetDaneshCriterion.integrableOn_cpow_mul_cexp_neg
#print axioms FleetDaneshCriterion.integral_pow_mul_exp_neg
#print axioms FleetDaneshCriterion.integral_cpow_mul_cexp_neg
#print axioms FleetDaneshCriterion.coeff_eq_zero_of_tendsto
#print axioms FleetDaneshCriterion.moment_identity
#print axioms FleetDaneshCriterion.moment_bound
#print axioms FleetDaneshCriterion.fiber_sum_eq_zero_of_growth
#print axioms FleetDaneshCriterion.zc_re
#print axioms FleetDaneshCriterion.zc_im
#print axioms FleetDaneshCriterion.abs_zc_re_lt
#print axioms FleetDaneshCriterion.summable_zc
#print axioms FleetDaneshCriterion.Sz_nonneg
#print axioms FleetDaneshCriterion.Decay.sq_le
#print axioms FleetDaneshCriterion.norm_term_le
#print axioms FleetDaneshCriterion.summable_term
#print axioms FleetDaneshCriterion.summable_norm_term
#print axioms FleetDaneshCriterion.norm_B_le
#print axioms FleetDaneshCriterion.norm_Q_le
#print axioms FleetDaneshCriterion.H_tr
#print axioms FleetDaneshCriterion.conj_cexp_neg_conj_mul
#print axioms FleetDaneshCriterion.term_tr
#print axioms FleetDaneshCriterion.B_tr
#print axioms FleetDaneshCriterion.Q_tr
#print axioms FleetDaneshCriterion.term_tr_right
#print axioms FleetDaneshCriterion.B_tr_right
#print axioms FleetDaneshCriterion.Decay.tr
#print axioms FleetDaneshCriterion.neg_conj_zc_of_RH
#print axioms FleetDaneshCriterion.cs_of_RH
#print axioms FleetDaneshCriterion.Q_real_nonneg_of_RH
#print axioms FleetDaneshCriterion.le_abs_of_not_mem_Icc
#print axioms FleetDaneshCriterion.H_eq_interval
#print axioms FleetDaneshCriterion.decay_of_bounds
#print axioms FleetDaneshCriterion.bounded_of_compact
#print axioms FleetDaneshCriterion.hasCompactSupport_of_supp
#print axioms FleetDaneshCriterion.decay_of_contDiff
#print axioms FleetDaneshCriterion.exists_bump
#print axioms FleetDaneshCriterion.chi_contDiff
#print axioms FleetDaneshCriterion.chi_nonneg
#print axioms FleetDaneshCriterion.chi_le_one
#print axioms FleetDaneshCriterion.chi_eq_zero
#print axioms FleetDaneshCriterion.chi_sum
#print axioms FleetDaneshCriterion.chi_supp
#print axioms FleetDaneshCriterion.chi_deriv_bound
#print axioms FleetDaneshCriterion.piece_contDiff
#print axioms FleetDaneshCriterion.piece_sum
#print axioms FleetDaneshCriterion.piece_supp
#print axioms FleetDaneshCriterion.piece_ne_zero
#print axioms FleetDaneshCriterion.piece_bounds
#print axioms FleetDaneshCriterion.integrable_cpx_mul_exp
#print axioms FleetDaneshCriterion.H_sum
#print axioms FleetDaneshCriterion.B_sum
#print axioms FleetDaneshCriterion.decay_of_Icc
#print axioms FleetDaneshCriterion.twoIntervalBound_of_RH
#print axioms FleetDaneshCriterion.H_zero_of_eq_zero
#print axioms FleetDaneshCriterion.B_eq_zero_left
#print axioms FleetDaneshCriterion.B_eq_zero_right
#print axioms FleetDaneshCriterion.pair_bound
#print axioms FleetDaneshCriterion.partition_cost
#print axioms FleetDaneshCriterion.growth_of_twoInterval
#print axioms FleetDaneshCriterion.fiber_sum_ne_zero
#print axioms FleetDaneshCriterion.half_sub_re_le_of_twoInterval
#print axioms FleetDaneshCriterion.abs_re_sub_half_le_of_twoInterval
#print axioms FleetDaneshCriterion.violation_of_offline_zero
#print axioms FleetDaneshCriterion.RH_iff_twoInterval
#print axioms FleetDaneshCriterion.widthFn_inv
#print axioms FleetDaneshCriterion.RH_iff_twoInterval_inv
-- FleetTwistedWindow: twisted Moebius polynomial and window for Dirichlet characters; L(s,chi) growth on Re >= 1/4 (Abel continuation); residue-free contour shift; local rectangle zero detection; twisted window rate c => zeros of L(s,chi) in |Re rho - 1/2| <= sqrt(2c) (primitive chi != 1); family beta* / D bounds (2026-11-11)
#print axioms FleetTwistedWindow.sum_range_eq_sum_univ
#print axioms FleetTwistedWindow.psum_mul_add
#print axioms FleetTwistedWindow.norm_psum_le
#print axioms FleetTwistedWindow.norm_ofReal_cpow'
#print axioms FleetTwistedWindow.norm_cpow_succ_sub_le
#print axioms FleetTwistedWindow.norm_abelTerm_le
#print axioms FleetTwistedWindow.differentiable_abelTerm
#print axioms FleetTwistedWindow.summable_abelTerm
#print axioms FleetTwistedWindow.differentiableOn_abelL
#print axioms FleetTwistedWindow.abel_partial
#print axioms FleetTwistedWindow.LSeries_eq_abelL
#print axioms FleetTwistedWindow.LFunction_eq_abel
#print axioms FleetTwistedWindow.norm_LFunction_le
#print axioms FleetTwistedWindow.norm_deriv_LFunction_le
#print axioms FleetTwistedWindow.MpolyChi_modOne
#print axioms FleetTwistedWindow.differentiable_MpolyChi
#print axioms FleetTwistedWindow.norm_moebius_chi_cpow_le
#print axioms FleetTwistedWindow.norm_MpolyChi_le
#print axioms FleetTwistedWindow.norm_deriv_L_line
#print axioms FleetTwistedWindow.continuous_deriv_L
#print axioms FleetTwistedWindow.integrable_line_chi
#print axioms FleetTwistedWindow.line_shift_entire
#print axioms FleetTwistedWindow.integrable_PhiChi_line
#print axioms FleetTwistedWindow.norm_fChi_strip_le
#print axioms FleetTwistedWindow.tendsto_horizontal_chi
#print axioms FleetTwistedWindow.headChi_eq_critical_line
#print axioms FleetTwistedWindow.Kc_nonneg
#print axioms FleetTwistedWindow.window_of_linear
#print axioms FleetTwistedWindow.norm_crit_integral_le
#print axioms FleetTwistedWindow.norm_headChi_le_of_windows
#print axioms FleetTwistedWindow.eventually_ne_zero_punctured_of_entire
#print axioms FleetTwistedWindow.finite_zeros
#print axioms FleetTwistedWindow.exists_factorization_entire
#print axioms FleetTwistedWindow.one_le_order_of_zero
#print axioms FleetTwistedWindow.rect_mem_nhds
#print axioms FleetTwistedWindow.differentiable_deriv_of_entire
#print axioms FleetTwistedWindow.continuousAt_logDeriv_mul
#print axioms FleetTwistedWindow.rect_logDeriv_residue
#print axioms FleetTwistedWindow.exp_detect
#print axioms FleetTwistedWindow.norm_LGw_le_two
#print axioms FleetTwistedWindow.norm_LGw_le_left
#print axioms FleetTwistedWindow.exp_tail_le
#print axioms FleetTwistedWindow.norm_LGw_le_tail
#print axioms FleetTwistedWindow.exists_bound_logDeriv_path
#print axioms FleetTwistedWindow.norm_right_edge_le
#print axioms FleetTwistedWindow.mem_rect_iff
#print axioms FleetTwistedWindow.div_four_mul_inv
#print axioms FleetTwistedWindow.one_le_sq_of_one_le
#print axioms FleetTwistedWindow.one_le_sq_of_le_neg_one
#print axioms FleetTwistedWindow.horiz_edge_le
#print axioms FleetTwistedWindow.vert_edge_le
#print axioms FleetTwistedWindow.detect_arith
#print axioms FleetTwistedWindow.zero_detect
#print axioms FleetTwistedWindow.norm_LSeries_le_of_re
#print axioms FleetTwistedWindow.abscissa_lt_three_halves
#print axioms FleetTwistedWindow.re_line
#print axioms FleetTwistedWindow.logDeriv_eq_neg_LSeries
#print axioms FleetTwistedWindow.norm_logDeriv_le_Bchi
#print axioms FleetTwistedWindow.norm_deriv_le_Kchi
#print axioms FleetTwistedWindow.Kchi_nonneg
#print axioms FleetTwistedWindow.MpolyChi_eq_sum_term
#print axioms FleetTwistedWindow.norm_inv_sub_MpolyChi_le
#print axioms FleetTwistedWindow.cut_tail_le
#print axioms FleetTwistedWindow.norm_primeLine_le_head
#print axioms FleetTwistedWindow.sqrt_exp_eq
#print axioms FleetTwistedWindow.zeros_right_of_twisted_window_rate
#print axioms FleetTwistedWindow.MpolyChi_inv_eq_conj
#print axioms FleetTwistedWindow.twistedWindow_inv
#print axioms FleetTwistedWindow.TwistedWindowRate.inv
#print axioms FleetTwistedWindow.gammaFactor_ne_zero
#print axioms FleetTwistedWindow.level_ne_one
#print axioms FleetTwistedWindow.LFunction_inv_one_sub_eq_zero
#print axioms FleetTwistedWindow.zeros_in_strip_of_twisted_window_rate
#print axioms FleetTwistedWindow.betaStar_le_of_uniform_rate
#print axioms FleetTwistedWindow.familyDev_le_of_uniform_rate
#print axioms FleetTwistedWindow.betaStarWithZeta_le

-- FleetPsiStripPerron, FleetPsiStrip: Perron/partial sums for coefficients << n^kappa; zero-free Re s > 1/2+delta => zeta'/zeta << log|t| (Borel-Caratheodory + Cauchy); StripBound delta => |psi(x) - x| <= C x^{1/2+delta+eps}; QuasiRH => x^{7/8+eps}; RH => x^{1/2+eps} (2026-11-11)
#print axioms FleetPsiStrip.perron_general'
#print axioms FleetPsiStrip.two_pi_Ssum'
#print axioms FleetPsiStrip.Ssum_diff_bound'
#print axioms FleetPsiStrip.Ssum_diff'
#print axioms FleetPsiStrip.partial_sum_bound'
#print axioms FleetPsiStrip.logDeriv_zeta_le
#print axioms FleetPsiStrip.logDeriv_zeta_bound
#print axioms FleetPsiStrip.psiG_alg
#print axioms FleetPsiStrip.psiG_eq
#print axioms FleetPsiStrip.psiG_differentiableAt
#print axioms FleetPsiStrip.psiG_differentiableAt_of_zeroFree
#print axioms FleetPsiStrip.vmCoeff_zero
#print axioms FleetPsiStrip.psiG_eq_LSeries
#print axioms FleetPsiStrip.norm_vmCoeff_le
#print axioms FleetPsiStrip.psiPrimeSide_eq_chebyshev_psi
#print axioms FleetPsiStrip.sum_vmCoeff
#print axioms FleetPsiStrip.psiG_bound
#print axioms FleetPsiStrip.psi_error_of_stripBound
#print axioms FleetPsiStrip.psi_error_of_quasiRH
#print axioms FleetPsiStrip.psi_error_of_RH
-- FleetWeilCriterion/Convolution/Archimedean/Positivity/OffLine/RH: Formal Conjectures' weil_positivity_criterion (google-deepmind/formal-conjectures a425ca3e, Apache-2.0) proved both directions; FC weilArchimedean = -standardArchimedean (2026-11-11)
#print axioms FleetWeilCriterion.weilPositivityCriterion_iff
#print axioms FleetWeilCriterion.auto_apply
#print axioms FleetWeilCriterion.exists_radius
#print axioms FleetWeilCriterion.hasCompactSupport_of_radius
#print axioms FleetWeilCriterion.auto_vanish
#print axioms FleetWeilCriterion.auto_contDiff
#print axioms FleetWeilCriterion.integrable_fubini
#print axioms FleetWeilCriterion.ft_auto
#print axioms FleetWeilCriterion.ft_neg_half_I
#print axioms FleetWeilCriterion.ft_half_I
#print axioms FleetWeilCriterion.ft_conj
#print axioms FleetWeilCriterion.ft_mul_ft_neg_real
#print axioms FleetWeilCriterion.deriv_vanish
#print axioms FleetWeilCriterion.hfun_eq_integral
#print axioms FleetWeilCriterion.hfun_ofReal_eq_ft
#print axioms FleetWeilCriterion.isTestFn_of_vanish
#print axioms FleetWeilCriterion.re_inv_term
#print axioms FleetWeilCriterion.digammaWeight_eq
#print axioms FleetWeilCriterion.dk_eq
#print axioms FleetWeilCriterion.abs_dk_le
#print axioms FleetWeilCriterion.summable_dk
#print axioms FleetWeilCriterion.continuous_dk
#print axioms FleetWeilCriterion.Admissible.vanishC
#print axioms FleetWeilCriterion.Admissible.supp
#print axioms FleetWeilCriterion.Admissible.contDiffC
#print axioms FleetWeilCriterion.Admissible.isTestFn
#print axioms FleetWeilCriterion.Admissible.continuous
#print axioms FleetWeilCriterion.Admissible.deriv
#print axioms FleetWeilCriterion.Admissible.deriv_cF
#print axioms FleetWeilCriterion.Admissible.hfun_deriv2
#print axioms FleetWeilCriterion.Admissible.integrable_hfun
#print axioms FleetWeilCriterion.Admissible.continuous_hfun
#print axioms FleetWeilCriterion.Admissible.integrable_weighted
#print axioms FleetWeilCriterion.integral_hfun_mul_tsum
#print axioms FleetWeilCriterion.exp_neg_abs_le
#print axioms FleetWeilCriterion.integrable_exp_neg_abs
#print axioms FleetWeilCriterion.lorentz_integral
#print axioms FleetWeilCriterion.Admissible.integrable_cF
#print axioms FleetWeilCriterion.Admissible.integral_hfun_mul_exp
#print axioms FleetWeilCriterion.Admissible.bounded
#print axioms FleetWeilCriterion.Admissible.integral_exp_abs_mul_neg
#print axioms FleetWeilCriterion.Admissible.lorentz_pairing
#print axioms FleetWeilCriterion.Admissible.integrableOn_mul_exp
#print axioms FleetWeilCriterion.Admissible.term_k
#print axioms FleetWeilCriterion.Admissible.lipschitz_zero
#print axioms FleetWeilCriterion.Admissible.abs_phiW_le_lin
#print axioms FleetWeilCriterion.Admissible.abs_phiW_le_exp
#print axioms FleetWeilCriterion.Admissible.one_sub_exp_neg_two_ge
#print axioms FleetWeilCriterion.Admissible.continuousOn_Qf
#print axioms FleetWeilCriterion.Admissible.Qf_le
#print axioms FleetWeilCriterion.Admissible.integrableOn_Qf
#print axioms FleetWeilCriterion.Admissible.tsum_term
#print axioms FleetWeilCriterion.Admissible.integrableOn_phiW_div
#print axioms FleetWeilCriterion.weilArchimedean_eq
#print axioms FleetWeilCriterion.phiW_div_eq
#print axioms FleetWeilCriterion.integral_exp_div_one_add
#print axioms FleetWeilCriterion.integral_phiW_div
#print axioms FleetWeilCriterion.standardArchimedean_eq_neg_weilArchimedean
#print axioms FleetWeilCriterion.weilNonArchimedean_eq_fleet
#print axioms FleetWeilCriterion.primeSum_cast
#print axioms FleetWeilCriterion.explicit_formula_weilSum
#print axioms FleetWeilCriterion.Gt_zero_eq
#print axioms FleetWeilCriterion.Gt_one_eq
#print axioms FleetWeilCriterion.admissible_auto
#print axioms FleetWeilCriterion.weil_explicit_formula
#print axioms FleetWeilCriterion.ordinate_real_of_RH
#print axioms FleetWeilCriterion.weilSum_auto_nonpos_of_RH
#print axioms FleetWeilCriterion.weilPositivity_of_RH
#print axioms FleetWeilCriterion.OffLine.mem_Zsf
#print axioms FleetWeilCriterion.OffLine.ws_nonneg
#print axioms FleetWeilCriterion.OffLine.summable_ws
#print axioms FleetWeilCriterion.OffLine.norm_gH_far
#print axioms FleetWeilCriterion.OffLine.norm_gH_le
#print axioms FleetWeilCriterion.OffLine.summable_weighted
#print axioms FleetWeilCriterion.OffLine.tail_bound
#print axioms FleetWeilCriterion.OffLine.tsum_split
#print axioms FleetWeilCriterion.OffLine.exists_gap
#print axioms FleetWeilCriterion.OffLine.vE_conj
#print axioms FleetWeilCriterion.OffLine.thetaE_conj
#print axioms FleetWeilCriterion.OffLine.exists_dominant
#print axioms FleetWeilCriterion.OffLine.exists_cos_eq_neg_one
#print axioms FleetWeilCriterion.OffLine.re_mul_exp
#print axioms FleetWeilCriterion.OffLine.false_of_dominant
#print axioms FleetWeilCriterion.WeilRH.integrable_ft_integrand
#print axioms FleetWeilCriterion.WeilRH.ft_sub
#print axioms FleetWeilCriterion.WeilRH.ft_add
#print axioms FleetWeilCriterion.WeilRH.ft_const_mul
#print axioms FleetWeilCriterion.WeilRH.ft_translate
#print axioms FleetWeilCriterion.WeilRH.bump_vanish
#print axioms FleetWeilCriterion.WeilRH.bump_admissible
#print axioms FleetWeilCriterion.WeilRH.probe_smooth
#print axioms FleetWeilCriterion.WeilRH.probe_vanish
#print axioms FleetWeilCriterion.WeilRH.ft_probe
#print axioms FleetWeilCriterion.WeilRH.isTestFunction_probe
#print axioms FleetWeilCriterion.WeilRH.re_ft_bump_pos
#print axioms FleetWeilCriterion.WeilRH.probe_isTestFn
#print axioms FleetWeilCriterion.WeilRH.ft_probe_eq_hfun
#print axioms FleetWeilCriterion.WeilRH.exists_ft_probe_bound
#print axioms FleetWeilCriterion.WeilRH.Wt_neg
#print axioms FleetWeilCriterion.WeilRH.ft_conj_general
#print axioms FleetWeilCriterion.WeilRH.Wt_conj
#print axioms FleetWeilCriterion.WeilRH.abs_im_tz_le
#print axioms FleetWeilCriterion.WeilRH.summable_norm_Wt
#print axioms FleetWeilCriterion.WeilRH.norm_cos_le
#print axioms FleetWeilCriterion.WeilRH.norm_cos_tz_le
#print axioms FleetWeilCriterion.WeilRH.summable_Wt_cos
#print axioms FleetWeilCriterion.WeilRH.trans_vanish
#print axioms FleetWeilCriterion.WeilRH.trans_smooth
#print axioms FleetWeilCriterion.WeilRH.ft_trans
#print axioms FleetWeilCriterion.WeilRH.isTestFunction_trans
#print axioms FleetWeilCriterion.WeilRH.ft_trans_mul
#print axioms FleetWeilCriterion.WeilRH.re_tsum_nonneg_of_weil
#print axioms FleetWeilCriterion.WeilRH.Phi_bound
#print axioms FleetWeilCriterion.WeilRH.integrable_gauss_mul
#print axioms FleetWeilCriterion.WeilRH.gaussHat_neg_alpha
#print axioms FleetWeilCriterion.WeilRH.integral_cos_mul_gauss
#print axioms FleetWeilCriterion.WeilRH.integrable_exp_abs_gauss
#print axioms FleetWeilCriterion.WeilRH.gauss_bound
#print axioms FleetWeilCriterion.WeilRH.strip_τ2
#print axioms FleetWeilCriterion.WeilRH.τ2_inl
#print axioms FleetWeilCriterion.WeilRH.τ2_inr
#print axioms FleetWeilCriterion.WeilRH.tsum_τ2
#print axioms FleetWeilCriterion.WeilRH.one_quarter_add_sq_ne
#print axioms FleetWeilCriterion.WeilRH.RH_of_weilPositivity
#print axioms FleetWeilCriterion.weil_positivity_criterion
-- FleetSquarefreeError: Q(N) = sum mu(d) floor(N/d^2); sum mu(n)/n^2 = 6/pi^2; hyperbola split; MoebiusSumBound theta (0<=theta<=1) => |Q(x) - 6x/pi^2| <= C x^{1/(3-theta)+eps}; QuasiRH => x^{8/17+eps}; RH => x^{2/5+eps} (2026-11-11)
#print axioms FleetSquarefreeError.sq_dvd_sq_mul_iff
#print axioms FleetSquarefreeError.sum_moebius_sq_dvd
#print axioms FleetSquarefreeError.sqfCount_eq
#print axioms FleetSquarefreeError.hasSum_moebius_div_sq
#print axioms FleetSquarefreeError.M_succ
#print axioms FleetSquarefreeError.sum_range_succ_eq_Ioc
#print axioms FleetSquarefreeError.M_eq_Ioc
#print axioms FleetSquarefreeError.abel
#print axioms FleetSquarefreeError.sum_rpow_tail_le
#print axioms FleetSquarefreeError.sum_rpow_head_le
#print axioms FleetSquarefreeError.rpow_div_sq
#print axioms FleetSquarefreeError.rpow_div_cube
#print axioms FleetSquarefreeError.inv_sq_sub_le
#print axioms FleetSquarefreeError.g_tail_le
#print axioms FleetSquarefreeError.floor_div_bounds
#print axioms FleetSquarefreeError.filter_eq_Ioc_sqrt
#print axioms FleetSquarefreeError.main_bound
#print axioms FleetSquarefreeError.bound_pow
#print axioms FleetSquarefreeError.squarefreeError_of_moebius
#print axioms FleetSquarefreeError.squarefreeError_of_quasiRH
#print axioms FleetSquarefreeError.squarefreeError_of_RH

-- 2026-11-11: Dirichlet 7/8 half-plane (hypothesis `DirichletQuasiRH`) ⇒ zero-free regions and least nonresidue
#print axioms FleetDirichletZeroFree.log_le_logQT
#print axioms FleetDirichletZeroFree.logQT_of_abs_le_one
#print axioms FleetDirichletZeroFree.log_pos_of_two_le
#print axioms FleetDirichletZeroFree.re_gt_of_region_strict
#print axioms FleetDirichletZeroFree.re_gt_of_region
#print axioms FleetDirichletZeroFree.region_subset_halfPlane_iff
#print axioms FleetDirichletZeroFree.LFunction_ne_zero_region_strict
#print axioms FleetDirichletZeroFree.LFunction_ne_zero_region
#print axioms FleetDirichletZeroFree.log_three_lt
#print axioms FleetDirichletZeroFree.log_four_lt
#print axioms FleetDirichletZeroFree.log_five_gt
#print axioms FleetDirichletZeroFree.six_four_lt_eight_div_log_three
#print axioms FleetDirichletZeroFree.five_six_lt_eight_div_log_four
#print axioms FleetDirichletZeroFree.eight_div_log_five_lt
#print axioms FleetDirichletZeroFree.LFunction_ne_zero_q_ge_three
#print axioms FleetDirichletZeroFree.LFunction_ne_zero_q_ge_five
#print axioms FleetDirichletZeroFree.LFunction_ne_zero_kadiri_shape
#print axioms FleetLeastNonresidue.LFunction_sub_one_norm_le
#print axioms FleetLeastNonresidue.norm_log_le_three
#print axioms FleetLeastNonresidue.logDeriv_LFunction_le
#print axioms FleetLeastNonresidue.twistVM_zero
#print axioms FleetLeastNonresidue.norm_twistVM_le
#print axioms FleetLeastNonresidue.norm_twistVM_le_rpow
#print axioms FleetLeastNonresidue.negLogDerivL_eq_LSeries
#print axioms FleetLeastNonresidue.negLogDerivL_differentiableAt
#print axioms FleetLeastNonresidue.S2_nonneg
#print axioms FleetLeastNonresidue.norm_negLogDerivL_le_of_re_ge
#print axioms FleetLeastNonresidue.negLogDerivL_bound
#print axioms FleetLeastNonresidue.norm_sum_twistVM_le
#print axioms FleetLeastNonresidue.legendreChar_apply
#print axioms FleetLeastNonresidue.legendreChar_ne_one
#print axioms FleetLeastNonresidue.legendreChar_eq_one_of_isSquare
#print axioms FleetLeastNonresidue.sum_twistVM_eq_psi
#print axioms FleetLeastNonresidue.quarter_le_psi
#print axioms FleetLeastNonresidue.exists_nonresidue_le_of_zeroFree
#print axioms FleetLeastNonresidue.exists_nonresidue_le_of_dirichletQuasiRH

-- FleetDeBruijnNewman: de Bruijn strip contraction for H_t = int_0^inf e^{tu^2} Phi(u) cos(zu) du (real-polynomial strip-approximable H_0); Lambda <= D/2; QuasiRH => zeros of xi(1/2+iz/2) in (Im z)^2 <= (3/4)^2; strip (3/4)^2 => Lambda <= 9/32 (2026-11-11)
#print axioms FleetDeBruijnNewman.root_factor_identity
#print axioms FleetDeBruijnNewman.eval_eq_prod
#print axioms FleetDeBruijnNewman.multiset_prod_bounds
#print axioms FleetDeBruijnNewman.ne_zero_of_stripZeros
#print axioms FleetDeBruijnNewman.shiftAvg_ne_zero_upper
#print axioms FleetDeBruijnNewman.shiftAvg_poly_strip
#print axioms FleetDeBruijnNewman.StripApprox.mono
#print axioms FleetDeBruijnNewman.StripApprox.of_limit
#print axioms FleetDeBruijnNewman.norm_add_I_mul_le
#print axioms FleetDeBruijnNewman.norm_sub_I_mul_le
#print axioms FleetDeBruijnNewman.StripApprox.shift
#print axioms FleetDeBruijnNewman.max_sub_le
#print axioms FleetDeBruijnNewman.StripApprox.iterate
#print axioms FleetDeBruijnNewman.StripApprox.differentiable
#print axioms FleetDeBruijnNewman.StripApprox.zeros
#print axioms FleetDeBruijnNewman.norm_cos_le
#print axioms FleetDeBruijnNewman.norm_cos_mul_le
#print axioms FleetDeBruijnNewman.continuous_integrand
#print axioms FleetDeBruijnNewman.Admissible.integrable_cos
#print axioms FleetDeBruijnNewman.Admissible.cosh_mul
#print axioms FleetDeBruijnNewman.Admissible.cosh_pow_mul
#print axioms FleetDeBruijnNewman.admissible_gauss
#print axioms FleetDeBruijnNewman.shiftAvg_cosT
#print axioms FleetDeBruijnNewman.iterate_shiftAvg_cosT
#print axioms FleetDeBruijnNewman.one_add_sq_div_two_le_cosh
#print axioms FleetDeBruijnNewman.cosh_pow_le
#print axioms FleetDeBruijnNewman.cosh_pow_tendsto
#print axioms FleetDeBruijnNewman.cosT_sub_norm_le
#print axioms FleetDeBruijnNewman.tendsto_weight_error
#print axioms FleetDeBruijnNewman.admissible_of_gauss
#print axioms FleetDeBruijnNewman.dbnH_zero_eq
#print axioms FleetDeBruijnNewman.stripApprox_dbnH
#print axioms FleetDeBruijnNewman.dbnH_at_zero_ne
#print axioms FleetDeBruijnNewman.deBruijn_strip
#print axioms FleetDeBruijnNewman.real_zeros_of_strip
#print axioms FleetDeBruijnNewman.Λ_le_of_strip
#print axioms FleetDeBruijnNewman.im_of_xi_param
#print axioms FleetDeBruijnNewman.quasiRH_xi_strip
#print axioms FleetDeBruijnNewman.Λ_le_nine_thirtyseconds
#print axioms FleetDeBruijnNewman.nine_thirtyseconds_gt_record

-- FleetSmoothWindow*: smooth Moebius window (weight e^{-b log^2 n}); unconditional rate 1/8; strip delta => rate delta^2/2+eps; 1/zeta = horizontal Gaussian average of P_b; S_b = Gaussian average of shifted smooth heads; smooth rate c => strip sqrt(2c); optimal smooth rate = D^2/2; RH <=> every positive smooth rate (2026-11-11)
#print axioms FleetSmoothWindow.summable_rpow_neg
#print axioms FleetSmoothWindow.Sz_nonneg
#print axioms FleetSmoothWindow.rpow_mul_exp_le
#print axioms FleetSmoothWindow.norm_term_le
#print axioms FleetSmoothWindow.summable_term
#print axioms FleetSmoothWindow.norm_Psm_le
#print axioms FleetSmoothWindow.term_eq
#print axioms FleetSmoothWindow.differentiable_term
#print axioms FleetSmoothWindow.differentiable_Psm
#print axioms FleetSmoothWindow.continuous_Psm
#print axioms FleetSmoothWindow.norm_Psm_half_le
#print axioms FleetSmoothWindow.integral_gauss_shift
#print axioms FleetSmoothWindow.integrable_window
#print axioms FleetSmoothWindow.smoothWindow_le
#print axioms FleetSmoothWindow.smoothWindowRate_one_eighth
#print axioms FleetSmoothWindow.rect_re_im
#print axioms FleetSmoothWindow.rect_zero
#print axioms FleetSmoothWindow.line_shift_zero
#print axioms FleetSmoothWindow.line_shift_one
#print axioms FleetSmoothWindow.half_strip_upper
#print axioms FleetSmoothWindow.half_strip_lower
#print axioms FleetSmoothWindow.tendsto_horiz_of_bound
#print axioms FleetSmoothWindow.integrable_of_gauss1
#print axioms FleetSmoothWindow.norm_cexp_quad
#print axioms FleetSmoothWindow.term_moebius_eq
#print axioms FleetSmoothWindow.norm_term_moebius_le
#print axioms FleetSmoothWindow.integral_term
#print axioms FleetSmoothWindow.integrable_term
#print axioms FleetSmoothWindow.integral_norm_term_le
#print axioms FleetSmoothWindow.Psm_eq_line
#print axioms FleetSmoothWindow.one_add_abs_le_exp_gauss
#print axioms FleetSmoothWindow.two_abs_le_exp_gauss
#print axioms FleetSmoothWindow.rpow_le_one_add
#print axioms FleetSmoothWindow.norm_gline_le
#print axioms FleetSmoothWindow.continuous_gline_line
#print axioms FleetSmoothWindow.integrable_gline_line
#print axioms FleetSmoothWindow.tendsto_horiz_gline
#print axioms FleetSmoothWindow.norm_Psm_half_le_of_zeroFree
#print axioms FleetSmoothWindow.smoothWindow_le_of_zeroFree
#print axioms FleetSmoothWindow.smoothWindowRate_mono
#print axioms FleetSmoothWindow.smoothWindowRate_of_zeroFree
#print axioms FleetSmoothWindow.smoothWindowRate_of_strip
#print axioms FleetSmoothWindow.smoothWindowRate_of_quasiRH
#print axioms FleetSmoothWindow.exp_neg_abs_le
#print axioms FleetSmoothWindow.gauss_max_le
#print axioms FleetSmoothWindow.gauss_term_eq
#print axioms FleetSmoothWindow.invZeta_eq_gauss
#print axioms FleetSmoothWindow.integrable_Fline
#print axioms FleetSmoothWindow.continuous_Fline
#print axioms FleetSmoothWindow.primeSumSym_eq_invZeta_line
#print axioms FleetSmoothWindow.norm_Psm_shift_le
#print axioms FleetSmoothWindow.integrable_xmaj
#print axioms FleetSmoothWindow.primeSumSym_eq_double
#print axioms FleetSmoothWindow.differentiable_Phix
#print axioms FleetSmoothWindow.differentiable_deriv_zetaReg
#print axioms FleetSmoothWindow.differentiableAt_deriv_zeta
#print axioms FleetSmoothWindow.differentiableAt_fx
#print axioms FleetSmoothWindow.continuousOn_fx
#print axioms FleetSmoothWindow.continuous_fx_line
#print axioms FleetSmoothWindow.continuous_fx_horiz
#print axioms FleetSmoothWindow.Ix_eq
#print axioms FleetSmoothWindow.norm_deriv_zeta_le_r
#print axioms FleetSmoothWindow.norm_deriv_zeta_le_lin
#print axioms FleetSmoothWindow.norm_deriv_zeta_le_Lam1
#print axioms FleetSmoothWindow.Lam1_le
#print axioms FleetSmoothWindow.Lam1_nonneg
#print axioms FleetSmoothWindow.norm_Phix_le
#print axioms FleetSmoothWindow.norm_fx_le
#print axioms FleetSmoothWindow.integrable_fx_line
#print axioms FleetSmoothWindow.tendsto_horiz_fx
#print axioms FleetSmoothWindow.Ix_eq_left
#print axioms FleetSmoothWindow.Ix_eq_right
#print axioms FleetSmoothWindow.Ix_eq_bump
#print axioms FleetSmoothWindow.K0_nonneg
#print axioms FleetSmoothWindow.window_lin_le
#print axioms FleetSmoothWindow.window_line_bound
#print axioms FleetSmoothWindow.residue_bound
#print axioms FleetSmoothWindow.gauss_four
#print axioms FleetSmoothWindow.gauss_lin_bound
#print axioms FleetSmoothWindow.rmm_line_bound
#print axioms FleetSmoothWindow.Gsum_le
#print axioms FleetSmoothWindow.bump_exp
#print axioms FleetSmoothWindow.bump_bound
#print axioms FleetSmoothWindow.Lam1_pos
#print axioms FleetSmoothWindow.inv_one_add_sq_ge
#print axioms FleetSmoothWindow.residue_final
#print axioms FleetSmoothWindow.region_a
#print axioms FleetSmoothWindow.region_b
#print axioms FleetSmoothWindow.region_c
#print axioms FleetSmoothWindow.region_d
#print axioms FleetSmoothWindow.Ix_bound
#print axioms FleetSmoothWindow.ae_ne_half
#print axioms FleetSmoothWindow.primeSumSym_le_of_smoothWindow
#print axioms FleetSmoothWindow.zeros_in_strip_of_smoothWindow
#print axioms FleetSmoothWindow.zeroDev_le_of_smoothWindowRate
#print axioms FleetSmoothWindow.smoothWindowRateInf_eq
#print axioms FleetSmoothWindow.not_smoothWindowRate_of_lt
#print axioms FleetSmoothWindow.RH_iff_smoothWindowRate
#print axioms FleetSmoothWindow.smoothWindowRateInf_le_of_quasiRH
#print axioms FleetSmoothWindow.smoothWindowRateInf_le_one_eighth

-- FleetExplicitPNTKernel/Bounds, FleetExplicitPNT: truncated Perron kernel with explicit error (port from kerr-lean EF, J. C. Kerr, Apache-2.0); explicit left-line, horizontal, low-zero and zero-sum constants; QuasiRH => |psi(x) - x| <= 12000 x^{7/8} log^2 x for x >= 1000 (2026-11-11)
#print axioms FleetExplicitPNTKernel.norm_hseg_le
#print axioms FleetExplicitPNTKernel.norm_vseg_le
#print axioms FleetExplicitPNTKernel.differentiable_const_cpow
#print axioms FleetExplicitPNTKernel.continuous_cpow_div_line
#print axioms FleetExplicitPNTKernel.kernel_rect_gt_one
#print axioms FleetExplicitPNTKernel.kernel_rect_lt_one
#print axioms FleetExplicitPNTKernel.le_of_forall_le_add_div
#print axioms FleetExplicitPNTKernel.norm_two_pi_inv
#print axioms FleetExplicitPNTKernel.kernel_gt_one
#print axioms FleetExplicitPNTKernel.kernel_lt_one
#print axioms FleetExplicitPNTKernel.neg_logDeriv_eq_tsum
#print axioms FleetExplicitPNTKernel.vonMangoldt_term_eq
#print axioms FleetExplicitPNTKernel.norm_vonMangoldt_term_le
#print axioms FleetExplicitPNTKernel.perron_integral_eq_tsum
#print axioms FleetExplicitPNTKernel.summable_kernel_terms
#print axioms FleetExplicitPNTKernel.S32_le
#print axioms FleetExplicitPNTKernel.halfint_log_bound
#print axioms FleetExplicitPNTKernel.norm_term_error_halfint
#print axioms FleetExplicitPNTKernel.psi_halfint_eq_tsum
#print axioms FleetExplicitPNTKernel.perron_error_halfint
#print axioms FleetExplicitPNTKernel.perron_small
#print axioms FleetExplicitPNTKernel.integral_inv_one_add_abs
#print axioms FleetExplicitPNTBounds.B_le
#print axioms FleetExplicitPNTBounds.norm_tan_three_halves
#print axioms FleetExplicitPNTBounds.norm_logDeriv_zeta_left_le
#print axioms FleetExplicitPNTBounds.sum_zetaOrder_low_le
#print axioms FleetExplicitPNTBounds.sum_inv_Icc_le_log
#print axioms FleetExplicitPNTBounds.sum_zetaOrder_div_norm_le
#print axioms FleetExplicitPNT.continuous_g0
#print axioms FleetExplicitPNT.Gt_g0
#print axioms FleetExplicitPNT.norm_G_le
#print axioms FleetExplicitPNT.Gt_g0_one
#print axioms FleetExplicitPNT.cpow_neg_eq_inv_cpow
#print axioms FleetExplicitPNT.right_edge_eq
#print axioms FleetExplicitPNT.norm_G_horiz_le
#print axioms FleetExplicitPNT.norm_G_left_le
#print axioms FleetExplicitPNT.horiz_edge_le
#print axioms FleetExplicitPNT.left_edge_le
#print axioms FleetExplicitPNT.zero_side_le
#print axioms FleetExplicitPNT.contour_algebra
#print axioms FleetExplicitPNT.num_perron
#print axioms FleetExplicitPNT.num_small
#print axioms FleetExplicitPNT.num_edge
#print axioms FleetExplicitPNT.num_left
#print axioms FleetExplicitPNT.num_zero
#print axioms FleetExplicitPNT.num_combine
#print axioms FleetExplicitPNT.heights_bounds
#print axioms FleetExplicitPNT.psi_halfint_explicit_of_quasiRH
#print axioms FleetExplicitPNT.psi_explicit_of_quasiRH

-- QuasiRHCorollaries: unconditional instances via quasiRH_holds (2026-11-11)

-- FleetSignUncertainty{Theory,Data,Cert1-3,}: +1 sign uncertainty constant (AlphaEvolve problem 11); Fourier eigenfunctions q(2pi x^2)e^{-pi x^2} via raising operators; exact Nat certificates (decide +kernel); explicit upper bound (2026-11-11)
#print axioms FleetSignUncertainty.evalN_addN
#print axioms FleetSignUncertainty.evalN_scaleN
#print axioms FleetSignUncertainty.hasDerivAt_pow_mul_evalN
#print axioms FleetSignUncertainty.hasDerivAt_evalN
#print axioms FleetSignUncertainty.evalP_addP
#print axioms FleetSignUncertainty.evalP_subP
#print axioms FleetSignUncertainty.evalP_scaleP
#print axioms FleetSignUncertainty.evalP_mulXP
#print axioms FleetSignUncertainty.hasDerivAt_evalP
#print axioms FleetSignUncertainty.integrable_pow_mul_gauss
#print axioms FleetSignUncertainty.integrable_pow_mul_evalN_gauss
#print axioms FleetSignUncertainty.integrable_pow_mul_evalP_gauss
#print axioms FleetSignUncertainty.integrable_phiE
#print axioms FleetSignUncertainty.integrable_phiO
#print axioms FleetSignUncertainty.integrable_x_mul_phiE
#print axioms FleetSignUncertainty.integrable_x_mul_phiO
#print axioms FleetSignUncertainty.hasDerivAt_gauss
#print axioms FleetSignUncertainty.hasDerivAt_evalP_sq
#print axioms FleetSignUncertainty.hasDerivAt_phiE
#print axioms FleetSignUncertainty.hasDerivAt_phiO
#print axioms FleetSignUncertainty.fourier_const_mul'
#print axioms FleetSignUncertainty.fourier_add'
#print axioms FleetSignUncertainty.fourier_sub'
#print axioms FleetSignUncertainty.fourier_raise
#print axioms FleetSignUncertainty.fourier_raise_eig
#print axioms FleetSignUncertainty.integrable_cE
#print axioms FleetSignUncertainty.integrable_cO
#print axioms FleetSignUncertainty.integrable_x_cE
#print axioms FleetSignUncertainty.integrable_x_cO
#print axioms FleetSignUncertainty.eig_even_to_odd
#print axioms FleetSignUncertainty.eig_odd_to_even
#print axioms FleetSignUncertainty.eig_Tstep
#print axioms FleetSignUncertainty.eig_const
#print axioms FleetSignUncertainty.eig_nil
#print axioms FleetSignUncertainty.eig_add
#print axioms FleetSignUncertainty.eig_hornerTP
#print axioms FleetSignUncertainty.evalN_mulLinN
#print axioms FleetSignUncertainty.evalN_addHeadN
#print axioms FleetSignUncertainty.evalN_compLinN
#print axioms FleetSignUncertainty.evalN_scaleUpN
#print axioms FleetSignUncertainty.leL_nonneg
#print axioms FleetSignUncertainty.tailOKP_pos
#print axioms FleetSignUncertainty.tail_pos
#print axioms FleetSignUncertainty.evalN_mulPowAux
#print axioms FleetSignUncertainty.evalN_append_single
#print axioms FleetSignUncertainty.evalN_reverse
#print axioms FleetSignUncertainty.evalN_zero
#print axioms FleetSignUncertainty.leafOK_pos
#print axioms FleetSignUncertainty.length_compLinN
#print axioms FleetSignUncertainty.length_mulPowAux
#print axioms FleetSignUncertainty.leavesOK_leaf
#print axioms FleetSignUncertainty.leavesOK_pos_aux
#print axioms FleetSignUncertainty.leavesOK_pos
#print axioms FleetSignUncertainty.lastSignChange_nonneg
#print axioms FleetSignUncertainty.lastSignChange_le
#print axioms FleetSignUncertainty.signUncertaintyConstant_le
#print axioms FleetSignUncertainty.evalP_pos_of_scaled
#print axioms FleetSignUncertainty.length_scaleUpN
#print axioms FleetSignUncertainty.chunk_leaves
#print axioms FleetSignUncertainty.chunk_tail
#print axioms FleetSignUncertainty.pos_glue
#print axioms FleetSignUncertainty.bound_of_certificate
#print axioms FleetSignUncertainty.hornerTP_sigR
#print axioms FleetSignUncertainty.sig_length
#print axioms FleetSignUncertainty.sig_zero
#print axioms FleetSignUncertainty.sigLeaves0
#print axioms FleetSignUncertainty.sigLeaves1
#print axioms FleetSignUncertainty.sigLeaves2
#print axioms FleetSignUncertainty.sigLeaves3
#print axioms FleetSignUncertainty.sigLeaves4
#print axioms FleetSignUncertainty.sigLeaves5
#print axioms FleetSignUncertainty.sigLeaves6
#print axioms FleetSignUncertainty.sigLeaves7
#print axioms FleetSignUncertainty.sigLeaves8
#print axioms FleetSignUncertainty.sigLeaves9
#print axioms FleetSignUncertainty.sigLeaves10
#print axioms FleetSignUncertainty.sigLeaves11
#print axioms FleetSignUncertainty.sigLeaves12
#print axioms FleetSignUncertainty.sigLeaves13
#print axioms FleetSignUncertainty.sigLeaves14
#print axioms FleetSignUncertainty.sigLeaves15
#print axioms FleetSignUncertainty.sigLeaves16
#print axioms FleetSignUncertainty.sigLeaves17
#print axioms FleetSignUncertainty.sigLeaves18
#print axioms FleetSignUncertainty.sigLeaves19
#print axioms FleetSignUncertainty.sigLeaves20
#print axioms FleetSignUncertainty.sigLeaves21
#print axioms FleetSignUncertainty.sigLeaves22
#print axioms FleetSignUncertainty.sigLeaves23
#print axioms FleetSignUncertainty.sigLeaves24
#print axioms FleetSignUncertainty.sigLeaves25
#print axioms FleetSignUncertainty.sigLeaves26
#print axioms FleetSignUncertainty.sigLeaves27
#print axioms FleetSignUncertainty.sigLeaves28
#print axioms FleetSignUncertainty.sigLeaves29
#print axioms FleetSignUncertainty.sigLeaves30
#print axioms FleetSignUncertainty.sigLeaves31
#print axioms FleetSignUncertainty.sigLeaves32
#print axioms FleetSignUncertainty.sigLeaves33
#print axioms FleetSignUncertainty.sigLeaves34
#print axioms FleetSignUncertainty.sigLeaves35
#print axioms FleetSignUncertainty.sigLeaves36
#print axioms FleetSignUncertainty.sigLeaves37
#print axioms FleetSignUncertainty.sigLeaves38
#print axioms FleetSignUncertainty.sigLeaves39
#print axioms FleetSignUncertainty.sigLeaves40
#print axioms FleetSignUncertainty.sigLeaves41
#print axioms FleetSignUncertainty.sigLeaves42
#print axioms FleetSignUncertainty.sigLeaves43
#print axioms FleetSignUncertainty.sigLeaves44
#print axioms FleetSignUncertainty.sigLeaves45
#print axioms FleetSignUncertainty.sigLeaves46
#print axioms FleetSignUncertainty.sigLeaves47
#print axioms FleetSignUncertainty.sigTail
#print axioms FleetSignUncertainty.sig_pos
#print axioms FleetSignUncertainty.signUncertaintyConstant_le_cert
#print axioms FleetSignUncertainty.signUncertaintyConstant_lt
#print axioms Kerr.PowerfulNumbers.divisor23_bound
#print axioms Kerr.PowerfulNumbers.mertens_bound_quasi
#print axioms Kerr.PowerfulNumbers.errorTermImprovement_of_quasiRH_only

-- 2026-11-12: FleetFirstZero: a zero of zeta at 1/2 + it, 14.13 < t < 14.14 (sign change of Lambda on the critical line; Euler-Maclaurin + kerr-lean rational discs + digamma bound, decide +kernel); FleetWindowLowerBound: headWindow b 1 >= pi sqrt b / Z1 for small b, no negative window rate
#print axioms FleetFirstZero.lcFOK_true
#print axioms FleetFirstZero.lcF_near
#print axioms FleetFirstZero.sq_re
#print axioms FleetFirstZero.sq_im
#print axioms FleetFirstZero.pwF_contains
#print axioms FleetFirstZero.sq_ne_one
#print axioms FleetFirstZero.main_contains
#print axioms FleetFirstZero.zeta_sub_main_le
#print axioms FleetFirstZero.zetaD_contains
#print axioms FleetFirstZero.Gammaℝ_eq_exp
#print axioms FleetFirstZero.abs_euler_le_one
#print axioms FleetFirstZero.norm_psiSeries_le
#print axioms FleetFirstZero.convex_Kset
#print axioms FleetFirstZero.half_mem_Kset
#print axioms FleetFirstZero.regLogGamma_sub_le
#print axioms FleetFirstZero.conjD_contains
#print axioms FleetFirstZero.signOK_true
#print axioms FleetFirstZero.Eg_diff_le
#print axioms FleetFirstZero.completedZeta_half_line_im
#print axioms FleetFirstZero.completedZeta_eq_mul
#print axioms FleetFirstZero.continuous_completedZeta_half_line
#print axioms FleetFirstZero.sq_eq
#print axioms FleetFirstZero.completedZeta_sign_change
#print axioms FleetFirstZero.exists_zeta_zero_first
#print axioms FleetFirstZero.exists_nontrivialZero_first
#print axioms FleetWindowLowerBound.differentiable_KZ
#print axioms FleetWindowLowerBound.decompZ
#print axioms FleetWindowLowerBound.rect_shiftZ
#print axioms FleetWindowLowerBound.line_shiftZ
#print axioms FleetWindowLowerBound.norm_zeta_strip_le
#print axioms FleetWindowLowerBound.norm_fZ_strip_le
#print axioms FleetWindowLowerBound.half_le_norm_line
#print axioms FleetWindowLowerBound.integrable_fZ_line
#print axioms FleetWindowLowerBound.tendsto_horizontalZ
#print axioms FleetWindowLowerBound.pairing_shift
#print axioms FleetWindowLowerBound.summable_add_one_rpow_neg
#print axioms FleetWindowLowerBound.innerZ_eq_line_integral
#print axioms FleetWindowLowerBound.Ssum_eq_line_integral
#print axioms FleetWindowLowerBound.card_divisors_le_two_sqrt
#print axioms FleetWindowLowerBound.sum_moebius_filter
#print axioms FleetWindowLowerBound.abs_kernel_le
#print axioms FleetWindowLowerBound.kernel_one
#print axioms FleetWindowLowerBound.abs_kernel_le_rpow
#print axioms FleetWindowLowerBound.abs_kernel_le_tail
#print axioms FleetWindowLowerBound.summable_kernel_bound
#print axioms FleetWindowLowerBound.abs_fk_le
#print axioms FleetWindowLowerBound.summable_fk
#print axioms FleetWindowLowerBound.moebius_mul_innerZ
#print axioms FleetWindowLowerBound.Ssum_eq_tsum
#print axioms FleetWindowLowerBound.sum_fk_eq
#print axioms FleetWindowLowerBound.summable_four_rpow
#print axioms FleetWindowLowerBound.abs_Ssum_sub_two_le
#print axioms FleetWindowLowerBound.tendsto_tailMaj
#print axioms FleetWindowLowerBound.norm_zeta_half_le
#print axioms FleetWindowLowerBound.Zq_pos
#print axioms FleetWindowLowerBound.continuous_zeta_half
#print axioms FleetWindowLowerBound.zeta_sq_le
#print axioms FleetWindowLowerBound.zeta_half_window
#print axioms FleetWindowLowerBound.cs_window
#print axioms FleetWindowLowerBound.mixI_le
#print axioms FleetWindowLowerBound.two_pi_norm_le
#print axioms FleetWindowLowerBound.norm_Phi_one_le
#print axioms FleetWindowLowerBound.sqrt_le_one_add
#print axioms FleetWindowLowerBound.tendsto_quad_exp
#print axioms FleetWindowLowerBound.tendsto_cut
#print axioms FleetWindowLowerBound.tendsto_err
#print axioms FleetWindowLowerBound.Zq_one
#print axioms FleetWindowLowerBound.Zq_neg_one
#print axioms FleetWindowLowerBound.Z1_pos
#print axioms FleetWindowLowerBound.headWindow_lower
#print axioms FleetWindowLowerBound.tendsto_exp_div_sqrt
#print axioms FleetWindowLowerBound.not_windowRate_of_neg
#print axioms FleetWindowLowerBound.windowRate_nonneg
#print axioms FleetWindowLowerBound.zeroDev_sq_half_le_of_windowRate
#print axioms FleetWindowLowerBound.not_windowRate_of_lt'
#print axioms FleetWindowLowerBound.sInf_windowRate_eq
#print axioms FleetWindowLowerBound.Mpoly_conj
#print axioms FleetWindowLowerBound.headWindow_neg
#print axioms FleetWindowLowerBound.headWindow_one_lower
-- 2026-11-12: Tier E formalized — weighted feasibility ⇒ RH (Laplace pole), heat monotonicity, Kronecker sharpness, Theorem 2 / composite positivity
#print axioms FleetLaplacePole.exists_pos_le_of_finite
#print axioms FleetLaplacePole.norm_cexp_neg_mul
#print axioms FleetLaplacePole.lap_differentiableAt
#print axioms FleetLaplacePole.lap_eq_tsum
#print axioms FleetLaplacePole.tsum_div_differentiableAt
#print axioms FleetLaplacePole.re_nonpos_of_bounded
#print axioms FleetWeightedLimit.decay
#print axioms FleetWeightedLimit.exists_bound_of_tendsto
#print axioms FleetWeightedLimit.norm_cexp_shift_le
#print axioms FleetWeightedLimit.one_add_sq_le
#print axioms FleetWeightedLimit.continuous_ext
#print axioms FleetWeightedLimit.oneBorel
#print axioms FleetWeightedLimit.kf_ofReal
#print axioms FleetWeightedLimit.continuous_kf
#print axioms FleetWeightedLimit.continuous_kf'
#print axioms FleetWeightedLimit.norm_kf_le
#print axioms FleetWeightedLimit.norm_kf'_le
#print axioms FleetWeightedLimit.tendsto_D
#print axioms FleetWeightedLimit.tendsto_kf
#print axioms FleetWeightedLimit.tendsto_gq
#print axioms FleetWeightedLimit.continuous_gq
#print axioms FleetWeightedLimit.tendsto_kf'
#print axioms FleetWeightedLimit.gB_apply
#print axioms FleetWeightedLimit.wmeas_univ
#print axioms FleetWeightedLimit.integral_wmeas
#print axioms FleetWeightedLimit.wmeas_real_univ
#print axioms FleetWeightedLimit.traceMap_eq
#print axioms FleetWeightedLimit.integral_wfin_gB
#print axioms FleetWeightedLimit.exists_limit
#print axioms FleetWeightedLimit.continuous_ext_kf
#print axioms FleetWeightedLimit.continuous_ext_kf'
#print axioms FleetWeightedLimit.hasDerivAt_kf
#print axioms FleetWeightedLimit.differentiable_Fm
#print axioms FleetWeightedLimit.Fm_rat
#print axioms FleetWeightedLimit.norm_kf_imag
#print axioms FleetWeightedLimit.norm_Fm_imag
#print axioms FleetWeightedLimit.exists_entire_realization
#print axioms FleetWeightedFeasibilityRH.u_re
#print axioms FleetWeightedFeasibilityRH.abs_u_im
#print axioms FleetWeightedFeasibilityRH.exp_neg_sq_div_eight_le
#print axioms FleetWeightedFeasibilityRH.norm_cexp_le
#print axioms FleetWeightedFeasibilityRH.summable_inv_u
#print axioms FleetWeightedFeasibilityRH.norm_term_le
#print axioms FleetWeightedFeasibilityRH.differentiable_Ztil
#print axioms FleetWeightedFeasibilityRH.summable_term
#print axioms FleetWeightedFeasibilityRH.gk_conj
#print axioms FleetWeightedFeasibilityRH.gaussHat_one
#print axioms FleetWeightedFeasibilityRH.Ztil_real
#print axioms FleetWeightedFeasibilityRH.Ztil_imag
#print axioms FleetWeightedFeasibilityRH.finite_window
#print axioms FleetWeightedFeasibilityRH.ordinates_real_of_entire_realization
#print axioms FleetWeightedFeasibilityRH.RH_of_weightedFeasible
#print axioms FleetWeightedFeasibilityRH.weightedFeasible_of_feasible
#print axioms FleetWeightedFeasibilityRH.RH_iff_weightedFeasible
#print axioms FleetWeightedFeasibilityRH.RH_iff_dualIneq
#print axioms FleetHeatMonotone.heatW_pos
#print axioms FleetHeatMonotone.integrable_heatW
#print axioms FleetHeatMonotone.integral_heatW
#print axioms FleetHeatMonotone.gaussHat_mul_heatW
#print axioms FleetHeatMonotone.integrable_gaussHat_mul_heatW
#print axioms FleetHeatMonotone.integral_gaussHat_mul_heatW
#print axioms FleetHeatMonotone.integral_real_heat
#print axioms FleetHeatMonotone.norm_gaussHat_mul_heatW
#print axioms FleetHeatMonotone.integral_norm_gaussHat_mul_heatW
#print axioms FleetHeatMonotone.integrable_tsum_of_summable
#print axioms FleetHeatMonotone.summable_integral_norm
#print axioms FleetHeatMonotone.aestronglyMeasurable_zeroTrace_mul
#print axioms FleetHeatMonotone.integrable_zeroTrace_mul_heatW
#print axioms FleetHeatMonotone.zeroTrace_heat_semigroup
#print axioms FleetHeatMonotone.rhs_heat_semigroup
#print axioms FleetHeatMonotone.zeroTrace_lower_bound_mono
#print axioms FleetHeatMonotone.rhs_lower_bound_mono
#print axioms FleetHeatMonotone.heatPositiveWidths_upward_closed
#print axioms FleetKroneckerSharpness.coeff_nonneg
#print axioms FleetKroneckerSharpness.coeff_eq
#print axioms FleetKroneckerSharpness.summable_coeff
#print axioms FleetKroneckerSharpness.summable_S
#print axioms FleetKroneckerSharpness.T_eq
#print axioms FleetKroneckerSharpness.S_le_T
#print axioms FleetKroneckerSharpness.abs_S_le_T
#print axioms FleetKroneckerSharpness.exists_aligned
#print axioms FleetKroneckerSharpness.exists_S_gt
#print axioms FleetKroneckerSharpness.isLUB_S
#print axioms FleetKroneckerSharpness.sSup_S
#print axioms FleetKroneckerSharpness.term_vonMangoldt_eq_real
#print axioms FleetKroneckerSharpness.primeSumSym_eq_S
#print axioms FleetKroneckerSharpness.primeSumSym_re_le
#print axioms FleetKroneckerSharpness.exists_primeSumSym_re_gt
#print axioms FleetPositivityComposite.e_gt
#print axioms FleetPositivityComposite.e_lt
#print axioms FleetPositivityComposite.exp_nat_ge
#print axioms FleetPositivityComposite.exp3_lt
#print axioms FleetPositivityComposite.two_pi_e3_lt
#print axioms FleetPositivityComposite.H_le_exp29
#print axioms FleetPositivityComposite.log29_le
#print axioms FleetPositivityComposite.log200_le
#print axioms FleetPositivityComposite.log6_le
#print axioms FleetPositivityComposite.big_lt_exp40
#print axioms FleetPositivityComposite.ordinate_real_of_PT
#print axioms FleetPositivityComposite.exists_conj_index
#print axioms FleetPositivityComposite.card_le_of_window
#print axioms FleetPositivityComposite.farW_nonneg
#print axioms FleetPositivityComposite.summable_farW
#print axioms FleetPositivityComposite.tail_le
#print axioms FleetPositivityComposite.pos_of_near
#print axioms FleetPositivityComposite.mainT_diff
#print axioms FleetPositivityComposite.finite_below
#print axioms FleetPositivityComposite.exists_zero_between
#print axioms FleetPositivityComposite.errT_le
#print axioms FleetPositivityComposite.near_zero_large
#print axioms FleetPositivityComposite.low_zero
#print axioms FleetPositivityComposite.theorem2
#print axioms FleetPositivityComposite.composite
#print axioms FleetPositivityComposite.composite_all_large_b
-- OAIExponentTrace: where 7/8 comes from in OpenAI's proof; HasCubicExponent ξ holds for all ξ ≥ 1; marked-capacity implication; general-c crossing algebra; balanced endpoint witness (2026-11-12)

-- 2026-11-12: FleetSmoothWindowLower: smoothWindow b 0 >= kappa sqrt b for small b (P_b(1/2) -> 1/zeta(1/2) by a contour through 1/2); no negative smooth window rate
#print axioms FleetSmoothWindowLower.integral_term_gauss
#print axioms FleetSmoothWindowLower.norm_term_le
#print axioms FleetSmoothWindowLower.coef_le
#print axioms FleetSmoothWindowLower.integral_Psm_gauss
#print axioms FleetSmoothWindowLower.zeta_ne_zero_box
#print axioms FleetSmoothWindowLower.invZeta_diff_box
#print axioms FleetSmoothWindowLower.isOpen_Ubox
#print axioms FleetSmoothWindowLower.diffOn_Ubox
#print axioms FleetSmoothWindowLower.exists_Kh
#print axioms FleetSmoothWindowLower.exists_L
#print axioms FleetSmoothWindowLower.invZeta_lip
#print axioms FleetSmoothWindowLower.hZ_one
#print axioms FleetSmoothWindowLower.exists_C
#print axioms FleetSmoothWindowLower.tail_pt
#print axioms FleetSmoothWindowLower.norm_setIntegral_le_full
#print axioms FleetSmoothWindowLower.split3
#print axioms FleetSmoothWindowLower.abs_mul_gauss_le
#print axioms FleetSmoothWindowLower.Psm_half_err
#print axioms FleetSmoothWindowLower.smoothWindow_zero_ge
#print axioms FleetSmoothWindowLower.invZeta_half_ne_zero
#print axioms FleetSmoothWindowLower.eventually_Psm_half_ge
#print axioms FleetSmoothWindowLower.kappa_pos
#print axioms FleetSmoothWindowLower.smoothWindow_lower
#print axioms FleetSmoothWindowLower.not_smoothWindowRate_of_neg
#print axioms FleetSmoothWindowLower.smoothWindowRate_nonneg
#print axioms FleetSmoothWindowLower.zeroDev_sq_half_le_of_smoothWindowRate
#print axioms FleetSmoothWindowLower.not_smoothWindowRate_of_lt'
#print axioms FleetSmoothWindowLower.sInf_smoothWindowRate_eq
