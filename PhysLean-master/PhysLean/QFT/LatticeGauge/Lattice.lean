/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Tactic.Abel

/-!
# Lattice gauge theory: the integer lattice as a quiver

This file provides the combinatorial base for lattice gauge theory on `ℤᵈ`:

- `LatticePoint d := Fin d → ℤ`
- a nearest-neighbour directed edge type `Edge d`
- a `Quiver` instance and basic lemmas about basis steps
-/

set_option autoImplicit false

namespace PhysLean
namespace QFT
namespace LatticeGauge

universe u

/-- A point of the integer lattice `ℤᵈ`. -/
abbrev LatticePoint (d : ℕ) := Fin d → ℤ

namespace LatticePoint

variable {d : ℕ}

/-- Standard basis vector `e_μ`. Corresponds to a unit displacement in direction `μ`. -/
@[simp] abbrev basisVec (μ : Fin d) : LatticePoint d :=
  Pi.single μ (1 : ℤ)

lemma basisVec_apply (μ i : Fin d) :
    basisVec (d := d) μ i = (if i = μ then 1 else 0) := by
  by_cases h : i = μ
  · subst h; simp [basisVec]
  · simp [basisVec, h]

@[simp]
lemma basisVec_same (μ : Fin d) : basisVec (d := d) μ μ = 1 := by
  simp [basisVec]

@[simp]
lemma basisVec_ne {μ i : Fin d} (h : i ≠ μ) : basisVec (d := d) μ i = 0 := by
  simp [basisVec, h]

instance : AddCommGroup (LatticePoint d) := by infer_instance

instance : Module ℤ (LatticePoint d) := by infer_instance

lemma add_basisVec_apply (p : LatticePoint d) (μ i : Fin d) :
    (p + basisVec (d := d) μ) i = p i + (if i = μ then 1 else 0) := by
  simp [basisVec_apply]

@[simp]
lemma add_basisVec_same (p : LatticePoint d) (μ : Fin d) :
    (p + basisVec (d := d) μ) μ = p μ + 1 := by
  simp

@[simp]
lemma add_basisVec_ne (p : LatticePoint d) {μ i : Fin d} (h : i ≠ μ) :
    (p + basisVec (d := d) μ) i = p i := by
  have : (if i = μ then (1 : ℤ) else 0) = 0 := by simp [h]
  simp [basisVec_apply, this]

@[simp]
lemma sub_add_basisVec (p : LatticePoint d) (μ : Fin d) :
    p - (p + basisVec (d := d) μ) = - basisVec (d := d) μ := by
  abel

@[simp]
lemma add_basisVec_sub (p : LatticePoint d) (μ : Fin d) :
    p + basisVec (d := d) μ - basisVec (d := d) μ = p := by
  abel

/-- Addition of basis vectors commutes, reflecting the geometry of the hypercubic lattice. -/
theorem add_basisVec_comm (p : LatticePoint d) (μ ν : Fin d) :
    p + basisVec μ + basisVec ν = p + basisVec ν + basisVec μ := by
  abel

end LatticePoint

open LatticePoint

/-! ### Nearest-neighbour directed edges -/

/-- Directed edges between nearest neighbours in `ℤᵈ`. -/
inductive Edge (d : ℕ) : LatticePoint d → LatticePoint d → Type
| fwd (p : LatticePoint d) (μ : Fin d) : Edge d p (p + basisVec μ)
| bwd (p : LatticePoint d) (μ : Fin d) : Edge d (p + basisVec μ) p

namespace Edge

variable {d : ℕ}

/-- A forward edge from `p` in direction `μ`. -/
@[match_pattern]
abbrev f (p : LatticePoint d) (μ : Fin d) : Edge d p (p + basisVec μ) :=
  Edge.fwd p μ

/-- A backward edge to `p` from direction `μ`. -/
@[match_pattern]
abbrev r (p : LatticePoint d) (μ : Fin d) : Edge d (p + basisVec μ) p :=
  Edge.bwd p μ

/-- The underlying lattice point used in the constructor. -/
def base {a b : LatticePoint d} : Edge d a b → LatticePoint d
  | Edge.fwd p _ => p
  | Edge.bwd p _ => p

/-- The coordinate direction used in the constructor. -/
def dir {a b : LatticePoint d} : Edge d a b → Fin d
  | Edge.fwd _ μ => μ
  | Edge.bwd _ μ => μ

/-- Orientation of an edge (`fwd`/`bwd`). -/
inductive Orient where | fwd | bwd

def orient {a b : LatticePoint d} : Edge d a b → Orient
  | Edge.fwd _ _ => Orient.fwd
  | Edge.bwd _ _ => Orient.bwd

@[simp]
lemma base_fwd (p : LatticePoint d) (μ : Fin d) :
    base (d := d) (Edge.fwd p μ) = p := rfl

@[simp]
lemma base_bwd (p : LatticePoint d) (μ : Fin d) :
    base (d := d) (Edge.bwd p μ) = p := rfl

@[simp]
lemma dir_fwd (p : LatticePoint d) (μ : Fin d) :
    dir (d := d) (Edge.fwd p μ) = μ := rfl

@[simp]
lemma dir_bwd (p : LatticePoint d) (μ : Fin d) :
    dir (d := d) (Edge.bwd p μ) = μ := rfl

@[simp]
lemma orient_fwd (p : LatticePoint d) (μ : Fin d) :
    orient (d := d) (Edge.fwd p μ) = Orient.fwd := rfl

@[simp]
lemma orient_bwd (p : LatticePoint d) (μ : Fin d) :
    orient (d := d) (Edge.bwd p μ) = Orient.bwd := rfl

/-- Reverse orientation of a directed edge. -/
def rev {a b : LatticePoint d} : Edge d a b → Edge d b a
  | Edge.fwd p μ => Edge.bwd p μ
  | Edge.bwd p μ => Edge.fwd p μ

@[simp]
lemma rev_fwd (p : LatticePoint d) (μ : Fin d) :
    rev (d := d) (Edge.fwd p μ) = Edge.bwd p μ := rfl

@[simp]
lemma rev_bwd (p : LatticePoint d) (μ : Fin d) :
    rev (d := d) (Edge.bwd p μ) = Edge.fwd p μ := rfl

@[simp]
lemma rev_rev {a b : LatticePoint d} (e : Edge d a b) :
    rev (d := d) (rev (d := d) e) = e := by
  cases e <;> rfl

@[simp] lemma base_rev {a b : LatticePoint d} (e : Edge d a b) :
    base (d := d) (rev (d := d) e) = base (d := d) e := by
  cases e <;> rfl

@[simp] lemma dir_rev {a b : LatticePoint d} (e : Edge d a b) :
    dir (d := d) (rev (d := d) e) = dir (d := d) e := by
  cases e <;> rfl

end Edge

/-- Quiver instance where arrows are directed nearest-neighbour edges. -/
instance (d : ℕ) : Quiver (LatticePoint d) where
  Hom := Edge d

/-! We can reverse any lattice edge, and reversing twice is the identity. This allows use of
`Quiver.Path.reverse` from `Mathlib.Combinatorics.Quiver.Symmetric`. -/
instance (d : ℕ) : Quiver.HasInvolutiveReverse (LatticePoint d) where
  reverse' := fun {a b} e => Edge.rev (d := d) e
  inv' := by
    intro a b e
    cases e <;> rfl

@[simp]
theorem quiver_reverse_fwd {d : ℕ} (p : LatticePoint d) (μ : Fin d) :
    Quiver.reverse (V := LatticePoint d) (a := p) (b := p + basisVec μ) (Edge.fwd p μ) =
      Edge.bwd p μ :=
  rfl

@[simp]
theorem quiver_reverse_bwd {d : ℕ} (p : LatticePoint d) (μ : Fin d) :
    Quiver.reverse (V := LatticePoint d) (a := p + basisVec μ) (b := p) (Edge.bwd p μ) =
      Edge.fwd p μ :=
  rfl

/-- The origin in `ℤᵈ`. -/
@[simp]
def origin (d : ℕ) : LatticePoint d := 0

end LatticeGauge
end QFT
end PhysLean
