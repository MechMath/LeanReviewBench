module

public import dep.CoarseDeGiorgi.Assembly.ClassicalMomentsSeries
public import dep.CoarseDeGiorgi.Statements.LowerCellAverage
public import dep.CoarseDeGiorgi.Statements.LowerMoment
public import dep.CoarseDeGiorgi.Statements.LowerResponseInvOnCell
public import dep.CoarseDeGiorgi.Statements.OriginCube
public import dep.CoarseDeGiorgi.Statements.SimplexCellSubsetOriginCube
public import dep.CoarseDeGiorgi.Statements.TriangulationCard
public import dep.CoarseDeGiorgi.Statements.UpperCellAverage
public import dep.CoarseDeGiorgi.Statements.UpperMoment
public import dep.CoarseDeGiorgi.Statements.UpperResponseOnCell
public import dep.CoarseDeGiorgi.LowerFractional.CompactCover
public import dep.CoarseDeGiorgi.Weighted.LowerSpecNorm
public import dep.CoarseDeGiorgi.Weighted.ResponseBoundsLower
public import dep.CoarseDeGiorgi.Weighted.UpperSpecHarmonic
public import dep.CoarseDeGiorgi.Weighted.UpperSpecNorm
public import dep.CoarseDeGiorgi.Weighted.ZeroBoundary
public import Mathlib.Analysis.CStarAlgebra.Matrix

@[expose] public section

namespace CoarseDeGiorgi.Harnack.Moments

open Homogenization MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

private theorem halfPower_sq (x : ENNReal) : (x.rpow (1 / 2)) ^ 2 = x := by
  simpa using Assembly.ClassicalMomentsImpl.half_power_sq x (p := 1) (by norm_num)

end CoarseDeGiorgi.Harnack.Moments
