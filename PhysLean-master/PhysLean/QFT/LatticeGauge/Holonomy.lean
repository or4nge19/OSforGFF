/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.QFT.LatticeGauge.Lattice

/-!
# Lattice gauge theory: holonomy along paths and plaquettes

This file defines:

- `GaugeField d G` as link variables on positively oriented edges,
- `edgeWeight` on directed edges (forward uses `U`, backward uses inversion),
- `parallelTransport` along `Quiver.Path`,
- elementary plaquette loops and the associated `wilsonLoop`.
-/

set_option autoImplicit false

namespace PhysLean
namespace QFT
namespace LatticeGauge

open LatticePoint

universe u

variable {d : ℕ} {G : Type u} [Group G]

/-- A gauge field assigns a group element to each positively oriented link `(p, μ)`. -/
abbrev GaugeField (d : ℕ) (G : Type u) := (LatticePoint d × Fin d) → G

/-- Transport an edge along definitional equalities of endpoints. -/
def castEdge {a b a' b' : LatticePoint d} (ha : a = a') (hb : b = b') (e : a ⟶ b) : a' ⟶ b' := by
  cases ha
  cases hb
  exact e

@[simp] lemma castEdge_rfl {a b : LatticePoint d} (e : a ⟶ b) :
    castEdge (d := d) (a := a) (b := b) rfl rfl e = e := by
  rfl

/-- The weight of a directed edge under a gauge field `U`. -/
def edgeWeight (U : GaugeField d G) {a b : LatticePoint d} (e : a ⟶ b) : G :=
  match e with
  | Edge.fwd p μ => U (p, μ)
  | Edge.bwd p μ => (U (p, μ))⁻¹

@[simp]
lemma edgeWeight_fwd (U : GaugeField d G) (p : LatticePoint d) (μ : Fin d) :
    edgeWeight (d := d) (G := G) U (Edge.fwd p μ) = U (p, μ) := rfl

@[simp]
lemma edgeWeight_bwd (U : GaugeField d G) (p : LatticePoint d) (μ : Fin d) :
    edgeWeight (d := d) (G := G) U (Edge.bwd p μ) = (U (p, μ))⁻¹ := rfl

@[simp]
lemma edgeWeight_f (U : GaugeField d G) (p : LatticePoint d) (μ : Fin d) :
    edgeWeight (d := d) (G := G) U (Edge.f p μ) = U (p, μ) := rfl

@[simp]
lemma edgeWeight_r (U : GaugeField d G) (p : LatticePoint d) (μ : Fin d) :
    edgeWeight (d := d) (G := G) U (Edge.r p μ) = (U (p, μ))⁻¹ := rfl

@[simp]
lemma edgeWeight_castEdge (U : GaugeField d G)
    {a b a' b' : LatticePoint d} (ha : a = a') (hb : b = b') (e : a ⟶ b) :
    edgeWeight U (castEdge (d := d) ha hb e) = edgeWeight U e := by
  cases ha; cases hb; rfl

@[simp]
lemma edgeWeight_castEdge_bwd (U : GaugeField d G) (q : LatticePoint d) (μ : Fin d)
    {a' : LatticePoint d} (ha : q + basisVec μ = a') :
    edgeWeight U (castEdge (d := d) ha rfl (Edge.bwd q μ)) = (U (q, μ))⁻¹ := by
  simpa [edgeWeight] using
    (edgeWeight_castEdge (d := d) (G := G) (U := U) ha rfl (Edge.bwd q μ))

/-- Product of edge weights along a path. -/
def pathProduct (U : GaugeField d G) {a b : LatticePoint d} : Quiver.Path a b → G
  | Quiver.Path.nil => 1
  | Quiver.Path.cons p e => pathProduct U p * edgeWeight U e

/-- `pathProduct` of a composed path splits as a product. -/
lemma pathProduct_comp (U : GaugeField d G) {a b c : LatticePoint d}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    pathProduct U (p.comp q) = pathProduct U p * pathProduct U q := by
  induction q with
  | nil =>
      simp [pathProduct]
  | cons q e ih =>
      simp [Quiver.Path.comp, pathProduct, ih, mul_assoc]

@[simp]
lemma pathProduct_toPath (U : GaugeField d G) {a b : LatticePoint d} (e : a ⟶ b) :
    pathProduct U e.toPath = edgeWeight U e := by
  simp [Quiver.Hom.toPath, pathProduct]

/-- Edge weights on reversed edges are inverted. -/
@[simp]
lemma edgeWeight_reverse (U : GaugeField d G) {a b : LatticePoint d} (e : a ⟶ b) :
    edgeWeight U (Quiver.reverse e) = (edgeWeight U e)⁻¹ := by
  cases e with
  | fwd p μ =>
      simp [edgeWeight, quiver_reverse_fwd]
  | bwd p μ =>
      simp [edgeWeight, quiver_reverse_bwd]

/-- The product along a reversed path is the inverse product. -/
lemma pathProduct_reverse (U : GaugeField d G) {a b : LatticePoint d} (p : Quiver.Path a b) :
    pathProduct U p.reverse = (pathProduct U p)⁻¹ := by
  induction p with
  | nil =>
      simp [Quiver.Path.reverse, pathProduct]
  | cons p e ih =>
      -- `Path.reverse` reverses order, so we use `pathProduct_comp`.
      simp [Quiver.Path.reverse, pathProduct_comp, pathProduct, ih, mul_inv_rev]

/-- Parallel transport along a path. -/
@[simp]
def parallelTransport (U : GaugeField d G) {a b : LatticePoint d}
    (p : Quiver.Path a b) : G :=
  pathProduct U p

@[simp] lemma parallelTransport_comp (U : GaugeField d G) {a b c : LatticePoint d}
    (p : Quiver.Path a b) (q : Quiver.Path b c) :
    parallelTransport U (p.comp q) = parallelTransport U p * parallelTransport U q := by
  simpa [parallelTransport] using pathProduct_comp (d := d) (G := G) (U := U) p q

lemma parallelTransport_reverse (U : GaugeField d G) {a b : LatticePoint d} (p : Quiver.Path a b) :
    parallelTransport U p.reverse = (parallelTransport U p)⁻¹ := by
  simpa [parallelTransport] using pathProduct_reverse (d := d) (G := G) (U := U) p

/-- The path around an elementary plaquette based at `p` in the `μ`–`ν` plane. -/
def plaquette (p : LatticePoint d) (μ ν : Fin d) : Quiver.Path p p :=
  let e₁ := Edge.fwd p μ
  let e₂ := Edge.fwd (p + basisVec μ) ν
  -- `Edge.bwd (p+e_ν) μ` has source `p+e_ν+e_μ`; cast it to `p+e_μ+e_ν`.
  let e₃ := castEdge (d := d)
      (LatticePoint.add_basisVec_comm (p := p) ν μ) rfl
      (Edge.bwd (p + basisVec ν) μ)
  let e₄ := Edge.bwd p ν
  ((Quiver.Path.nil : Quiver.Path p p).cons e₁).cons e₂ |>.cons e₃ |>.cons e₄

/-- The Wilson loop is the parallel transport around a plaquette. -/
def wilsonLoop (U : GaugeField d G) (p : LatticePoint d) (μ ν : Fin d) (_h : μ ≠ ν) : G :=
  parallelTransport U (plaquette p μ ν)

/-- Explicit expansion of the Wilson loop. -/
lemma wilsonLoop_expansion (U : GaugeField d G) (p : LatticePoint d)
    (μ ν : Fin d) (h : μ ≠ ν) :
    wilsonLoop U p μ ν h =
      U (p, μ) *
      U (p + basisVec μ, ν) *
      (U (p + basisVec ν, μ))⁻¹ *
      (U (p, ν))⁻¹ := by
  unfold wilsonLoop plaquette parallelTransport
  simp [pathProduct, edgeWeight_castEdge, mul_assoc]

end LatticeGauge
end QFT
end PhysLean
