/-
Copyright (c) 2026 Michael Jarret. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Jarret
-/
module
public import UnitaryProducts.PaperProof.GapAdapted
public import UnitaryProducts.PaperProof.PrecessingSpin
public import UnitaryProducts.PaperProof.SpinProse
public import UnitaryProducts.PaperProof.SpinRemainders
public import UnitaryProducts.PaperProof.SpinConsequences
public import UnitaryProducts.PaperProof.BurgarthScaling
public import UnitaryProducts.PaperProof.LeftHeld
public import UnitaryProducts.PaperProof.OddResonance
public import UnitaryProducts.PaperProof.ExamplesProse
public import UnitaryProducts.PaperProof.Crossings
public import UnitaryProducts.Prose.Fidelity
public import UnitaryProducts.PaperProof.CorWalkLeakage
public import UnitaryProducts.PaperProof.ClosedCellLimit
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.RemovableSingularity
public import UnitaryProducts.Corrector.FrameMultiplier
public import UnitaryProducts.Walks.LogHessian
public import UnitaryProducts.Walks.WalkScalarCut
public import UnitaryProducts.PaperProof.WalkCutFormula
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
public import Mathlib.Topology.ContinuousMap.Units
public import UnitaryProducts.PaperProof.UnifiedDerivative
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import UnitaryProducts.PaperProof.MatrixSeries
public import Mathlib.MeasureTheory.Function.JacobianOneDim
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import UnitaryProducts.PaperProof.SpectralProofSteps
public import UnitaryProducts.PaperProof.AffineRescale
public import UnitaryProducts.PaperProof.UniformDerivativeSeries
public import UnitaryProducts.PaperProof.UniformConstants
public import Mathlib.Analysis.SpecialFunctions.Artanh

public import UnitaryProducts.PaperProof.AffineJumps
public import UnitaryProducts.PaperProof.CorProducts
public import UnitaryProducts.Paper.SpectralWindow
public import UnitaryProducts.Prose.UnitaryFactors
public import UnitaryProducts.Prose.CellMotivation
public import UnitaryProducts.Prose.Discussion

public import UnitaryProducts.PaperProof.RotatingFrame
public import UnitaryProducts.PaperProof.FrameUnitSteps
public import UnitaryProducts.Paper.UnitComparisonObjects
public import UnitaryProducts.PaperProof.ClosedCellCorrector
public import UnitaryProducts.PaperProof.CanonicalCell
public import UnitaryProducts.PaperProof.CenteredUnitSteps
public import UnitaryProducts.Paper.EvolutionAndFineSteps
public import UnitaryProducts.Comparison.SpectralWidth
public import UnitaryProducts.Corrector.PowerDerivative
public import UnitaryProducts.Comparison.EndpointConstants
public import UnitaryProducts.Corrector.FrameOperator
public import UnitaryProducts.Walks.LogMoving
public import UnitaryProducts.Comparison.UnitSteps
public import UnitaryProducts.Walks.LogarithmDerivativeBounds
public import UnitaryProducts.Evolution.RoundedClockEvolution
public import UnitaryProducts.Paper.OneVariable
public import UnitaryProducts.Comparison.OneSize
public import UnitaryProducts.Paper.Preliminaries
public import UnitaryProducts.Evolution.RegulatedComparison
public import UnitaryProducts.Spectral.CircularBands
public import UnitaryProducts.Spectral.SinTheta
public import UnitaryProducts.Evolution.RegulatedExistence
public import UnitaryProducts.Paper.FineStepBounds
public import UnitaryProducts.Approximation.MidpointError
public import UnitaryProducts.Spectral.BandTransfer
public import UnitaryProducts.Spectral.TrackedBandGap
public import UnitaryProducts.Comparison.EndpointComparison
public import UnitaryProducts.Corrector.FrameBounds
public import UnitaryProducts.Spectral.WidthAndGap
public import UnitaryProducts.Walks.SharpComparison
public import UnitaryProducts.Evolution.Simulation
public import UnitaryProducts.Corrector.ScalarEntrySolutions
public import UnitaryProducts.Comparison.SharpInT
public import UnitaryProducts.Approximation.EntryRounding
public import UnitaryProducts.Prose.WalkComparisonJRS
public import UnitaryProducts.Prose.ChainSteps
public import UnitaryProducts.Prose.ResidualPointwise
public import UnitaryProducts.Prose.LocalSteps
public import UnitaryProducts.Prose.RoundedClockQuarter
public import UnitaryProducts.Prose.UnitStepsWalks
public import UnitaryProducts.Prose.WalkLogLocal
public import UnitaryProducts.Prose.FineSteps
public import UnitaryProducts.Prose.Introduction
public import UnitaryProducts.Prose.Preliminaries
public import UnitaryProducts.Prose.UnitStepsCorrector
public import UnitaryProducts.Prose.FinalSteps
public import UnitaryProducts.PaperProof.ExTruncationBits
public import UnitaryProducts.PaperProof.FactAdjoint
public import UnitaryProducts.Corrector.PeriodicCharacterization
public import UnitaryProducts.PaperProof.LemWalkLog
public import UnitaryProducts.PaperProof.ThmComparison
public import UnitaryProducts.PaperProof.ThmTransfer
public import UnitaryProducts.PaperProof.RemTruncatedEndpoints
public import UnitaryProducts.PaperProof.UniformConsequences
public import UnitaryProducts.Prose.SyncSteps
public import UnitaryProducts.PaperProof.UniformComparison
public import UnitaryProducts.PaperProof.ThmUnitStepsMax

public import UnitaryProducts.PaperProof.IntroTheorems

public import UnitaryProducts.Prose.UnitTransfer

public import UnitaryProducts.PaperProof.UnitExamples
public import UnitaryProducts.PaperProof.UniformCells
public import UnitaryProducts.PaperProof.UniformTruncation

public import UnitaryProducts.PaperProof.UniformCellGeometry

public import UnitaryProducts.PaperProof.OscillationFineSteps

public import UnitaryProducts.PaperProof.UniformCellIntegrals

public import UnitaryProducts.PaperProof.UnitRounded
public import UnitaryProducts.Prose.SharpnessExpansion
public import UnitaryProducts.Prose.GeneralSpectralSeries
public import UnitaryProducts.Prose.ShiftedEvolution

public import UnitaryProducts.PaperProof.PrincipalLog
public import UnitaryProducts.PaperProof.PeriodicSpectrum

import UnitaryProducts.PaperProof.ExponentialDefinitions

public import UnitaryProducts.PaperProof.PropTransfer
public import UnitaryProducts.Prose.ExactCorrection

public import UnitaryProducts.PaperProof.CellEquations

public import UnitaryProducts.Prose.UnifiedQuadrature
public import UnitaryProducts.PaperProof.UnifiedJumpsSupport

public import UnitaryProducts.PaperProof.LemWalkBands
public import UnitaryProducts.Walks.TrackedBandMultiplicity
public import UnitaryProducts.PaperProof.ProductCoefficients

/-!
# Products of unitaries

The paper's formal development, collected in section order.

## Main results

See `UnitaryProducts.PaperProof.IntroTheorems` for Theorem B and
`THEOREMS.md` for the complete statement index, including the three examples.

## References

Michael Jarret, *Products of unitaries as continuous evolutions at finite precision*.
-/

