import PhysLean.QFT.LatticeGauge.Lattice
import PhysLean.QFT.LatticeGauge.Holonomy
import PhysLean.QFT.LatticeGauge.GaugeTransform
import PhysLean.QFT.LatticeGauge.Abelian

/-!
# Lattice gauge theory (core)

Import hub for the current PR-ready core of lattice gauge theory:

- the lattice as a quiver (`LatticePoint`, `Edge`, paths),
- holonomy / Wilson loops,
- gauge transformations and covariance,
- abelian identities (e.g. lattice Bianchi).

The harder topological results (e.g. discrete Poincaré lemma `flat → pure gauge`) are intentionally
kept out of this core until they are fully proved.
-/

set_option autoImplicit false

