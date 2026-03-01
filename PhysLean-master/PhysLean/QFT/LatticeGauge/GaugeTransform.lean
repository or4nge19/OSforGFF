/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import PhysLean.QFT.LatticeGauge.Holonomy
import Mathlib.Tactic.Group

/-!
# Lattice gauge theory: gauge transformations

This file defines pointwise gauge transformations and proves:

- edge weights transform by conjugation,
- parallel transport transforms covariantly,
- Wilson loops transform by conjugation,
- pure gauge implies trivial Wilson loops.
-/

set_option autoImplicit false

namespace PhysLean
namespace QFT
namespace LatticeGauge

open LatticePoint

universe u

variable {d : ℕ} {G : Type u} [Group G]

/-- A pointwise gauge transformation acts on link variables by conjugation at endpoints. -/
def gaugeTransform (U : GaugeField d G) (g : LatticePoint d → G) : GaugeField d G :=
  fun ⟨p, μ⟩ => g p * U (p, μ) * (g (p + basisVec μ))⁻¹

@[simp]
lemma gaugeTransform_apply (U : GaugeField d G) (g : LatticePoint d → G) (p : LatticePoint d)
    (μ : Fin d) :
    gaugeTransform (d := d) (G := G) U g (p, μ) = g p * U (p, μ) * (g (p + basisVec μ))⁻¹ :=
  rfl

@[simp]
lemma gaugeTransform_id (U : GaugeField d G) :
    gaugeTransform (d := d) (G := G) U (fun _ => (1 : G)) = U := by
  ext x
  rcases x with ⟨p, μ⟩
  simp [gaugeTransform]

lemma gaugeTransform_comp (U : GaugeField d G) (g₁ g₂ : LatticePoint d → G) :
    gaugeTransform (d := d) (G := G) (gaugeTransform (d := d) (G := G) U g₂) g₁ =
      gaugeTransform (d := d) (G := G) U (fun p => g₁ p * g₂ p) := by
  ext x
  rcases x with ⟨p, μ⟩
  simp [gaugeTransform, mul_assoc, mul_inv_rev]

/-- The identity gauge field. -/
@[simp]
def identityGaugeField : GaugeField d G := fun _ => 1

@[simp] lemma identityGaugeField_apply (x : LatticePoint d × Fin d) :
    identityGaugeField (d := d) (G := G) x = (1 : G) := rfl

/-- A gauge field is pure gauge if it is the gauge transform of the identity. -/
def IsPureGauge (U : GaugeField d G) : Prop :=
  ∃ (g : LatticePoint d → G), U = gaugeTransform (d := d) (G := G) (identityGaugeField (d := d) (G := G)) g

/-! ### Gauge transformations form an action -/

instance : MulAction (LatticePoint d → G) (GaugeField d G) where
  smul g U := gaugeTransform (d := d) (G := G) U g
  one_smul U := by
    -- unfold the action and use the explicit computation lemma
    change gaugeTransform (d := d) (G := G) U (fun _ => (1 : G)) = U
    exact gaugeTransform_id (d := d) (G := G) U
  mul_smul g₁ g₂ U := by
    -- (g₁ * g₂) • U = g₁ • (g₂ • U)
    -- The pointwise multiplication on `LatticePoint d → G` is the group structure.
    change
      gaugeTransform (d := d) (G := G) U (g₁ * g₂) =
        gaugeTransform (d := d) (G := G) (gaugeTransform (d := d) (G := G) U g₂) g₁
    -- `gaugeTransform_comp` is stated in the RHS form; rewrite and finish by ext/simp.
    ext x
    rcases x with ⟨p, μ⟩
    simp [gaugeTransform, Pi.mul_apply, mul_assoc, mul_inv_rev]

@[simp] lemma smul_def (g : LatticePoint d → G) (U : GaugeField d G) :
    g • U = gaugeTransform (d := d) (G := G) U g :=
  rfl

/-! ### Gauge equivalence and automorphisms -/

/-- Gauge equivalence: `U₂` is a gauge transform of `U₁`. -/
def GaugeEquiv (U₁ U₂ : GaugeField d G) : Prop :=
  ∃ g : LatticePoint d → G, U₂ = gaugeTransform (d := d) (G := G) U₁ g

@[refl]
lemma GaugeEquiv.refl (U : GaugeField d G) : GaugeEquiv (d := d) (G := G) U U :=
  ⟨fun _ => 1, (gaugeTransform_id (d := d) (G := G) U).symm⟩

@[trans]
lemma GaugeEquiv.trans {U₁ U₂ U₃ : GaugeField d G} :
    GaugeEquiv (d := d) (G := G) U₁ U₂ → GaugeEquiv (d := d) (G := G) U₂ U₃ →
      GaugeEquiv (d := d) (G := G) U₁ U₃ := by
  rintro ⟨g₁, rfl⟩ ⟨g₂, rfl⟩
  refine ⟨fun p => g₂ p * g₁ p, ?_⟩
  -- `GaugeEquiv` comp corresponds to pointwise multiplication.
  simp [gaugeTransform_comp]

/-- The gauge transform by a fixed `g` is an equivalence of gauge fields. -/
def gaugeTransformEquiv (g : LatticePoint d → G) : GaugeField d G ≃ GaugeField d G where
  toFun U := gaugeTransform (d := d) (G := G) U g
  invFun U := gaugeTransform (d := d) (G := G) U (fun p => (g p)⁻¹)
  left_inv U := by
    ext x
    rcases x with ⟨p, μ⟩
    simp [gaugeTransform, mul_assoc]
  right_inv U := by
    ext x
    rcases x with ⟨p, μ⟩
    simp [gaugeTransform, mul_assoc]

/-- Edge weights transform by conjugation under a gauge transformation. -/
lemma edgeWeight_gaugeTransform (U : GaugeField d G) (g : LatticePoint d → G) :
    ∀ {a b : LatticePoint d} (e : a ⟶ b),
      edgeWeight (gaugeTransform (d := d) (G := G) U g) e = g a * edgeWeight U e * (g b)⁻¹ := by
  intro a b e
  cases e with
  | fwd p μ =>
      simp [edgeWeight, gaugeTransform, mul_assoc]
  | bwd p μ =>
      simp [edgeWeight, gaugeTransform, mul_inv_rev, inv_inv, mul_assoc]

/-- Edge weights of the identity field are trivial. -/
@[simp]
lemma edgeWeight_id {a b : LatticePoint d} :
    ∀ (e : a ⟶ b), edgeWeight (identityGaugeField (d := d) (G := G)) e = (1 : G)
  | Edge.fwd _ _ => by simp [edgeWeight, identityGaugeField]
  | Edge.bwd _ _ => by simp [edgeWeight, identityGaugeField]

/-- Parallel transport transforms covariantly. -/
lemma parallelTransport_gaugeTransform (U : GaugeField d G) (g : LatticePoint d → G)
    {a b : LatticePoint d} (p : Quiver.Path a b) :
    parallelTransport (gaugeTransform (d := d) (G := G) U g) p =
      g a * parallelTransport U p * (g b)⁻¹ := by
  induction p with
  | nil =>
      simp [parallelTransport, pathProduct]
  | cons path edge ih =>
      simp only [parallelTransport, pathProduct] at ih ⊢
      simpa [mul_assoc] using by
        have := congrArg (fun x => x * edgeWeight (gaugeTransform (d := d) (G := G) U g) edge) ih
        simpa [edgeWeight_gaugeTransform, mul_assoc] using this

/-- Wilson loops transform by conjugation under gauge transformations. -/
theorem wilsonLoop_gaugeTransform_conj (U : GaugeField d G) (g : LatticePoint d → G)
    (p : LatticePoint d) (μ ν : Fin d) (h : μ ≠ ν) :
    wilsonLoop (gaugeTransform (d := d) (G := G) U g) p μ ν h =
      g p * wilsonLoop U p μ ν h * (g p)⁻¹ := by
  unfold wilsonLoop
  simpa using parallelTransport_gaugeTransform (d := d) (G := G) U g (plaquette p μ ν)

/-- A pure gauge configuration has trivial Wilson loops. -/
theorem wilsonLoops_trivial_of_pureGauge (U : GaugeField d G) :
    IsPureGauge (d := d) (G := G) U →
      ∀ (p : LatticePoint d) (μ ν : Fin d) (h : μ ≠ ν),
        wilsonLoop U p μ ν h = 1 := by
  rintro ⟨g, hg⟩ p μ ν h
  rw [hg, wilsonLoop_gaugeTransform_conj (d := d) (G := G)
        (U := identityGaugeField (d := d) (G := G)) (g := g)]
  simp [wilsonLoop_expansion]

end LatticeGauge
end QFT
end PhysLean
