import PhysLean.QFT.Euclidean.Model
import PhysLean.QFT.Euclidean.FieldConfiguration
import PhysLean.SpaceAndTime.SpaceTime.TimeDirection
import PhysLean.QFT.Euclidean.VectorValued
import PhysLean.QFT.Euclidean.GelfandTriple

/-!
# Euclidean QFT (core)

This file is an import hub for the minimal Euclidean-QFT-facing core API:

- `EuclideanQFTModel` (measure + axiom bundle),
- cylindrical measurable space on `WeakDual`,
- spacetime time-direction operations on Schwartz test functions,
- vector-valued Schwartz/distributions and internal symmetries,
- a minimal Gel'fand triple interface.
-/

