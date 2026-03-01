/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.MinlosGaussianSupportL2
import OSforGFF.MinlosGaussianSeminormBoundsStd
import OSforGFF.MinlosGaussianToWeakDual

import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Nuclear decomposition → a.s. support (Gaussian Minlos, `L²` route)

This file continues the `L²`-based support proof for the Kolmogorov Gaussian process measure.

Starting from the `L²`-evaluation operator on local Banach spaces (constructed in
`OSforGFF.MinlosGaussianSupportL2`), we precompose with a nuclear inclusion
`BanachOfSeminorm (p m) → BanachOfSeminorm (p n)` coming from `NuclearSpaceStd`. This yields a
**nuclear** operator into `L²`, hence a nuclear series representation.

That representation is then used to define a measurable modification of sample paths whose
realisations are continuous linear functionals, and to conclude that the Kolmogorov measure is
almost surely supported on `Set.range MinlosGaussianToWeakDual.toFun`.
-/

open scoped BigOperators ENNReal NNReal RealInnerProductSpace ProbabilityTheory

open MeasureTheory Filter Topology

namespace OSforGFF

noncomputable section

namespace MinlosGaussianSupport

open OSforGFF.MinlosGaussianKolmogorov
open OSforGFF.MinlosGaussianSeminormBoundsStd
open OSforGFF.NuclearSpaceStd

-- As in `MinlosGaussianSupportL2`, we prefer the seminorm-induced quotient topology.
attribute [-instance] QuotientModule.Quotient.topologicalSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [NuclearSpaceStd E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "μ[" T "]" =>
  gaussianProcess (E := E) (H := H) (T : E →ₗ[ℝ] H)

/-! ## The nuclear `L²` operator on a smaller Banach space -/

/-- Choose a seminorm `seminormFamily n` and constant `C` controlling `‖T ·‖`. -/
theorem exists_seminormFamily_bound (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧ (normSeminorm ℝ H).comp T ≤ C • seminormFamily (E := E) n :=
  exists_bound_seminormFamily (E := E) (H := H) T h_sq

/-- For a chosen seminorm bound on `‖T ·‖`, pick a strictly larger index `m` such that the
canonical inclusion `Banach_m → Banach_n` is nuclear. -/
theorem exists_nuclear_inclusion (n : ℕ) :
    ∃ m : ℕ, ∃ hnm : n < m,
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E)
          (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
          ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm))) := by
  classical
  rcases NuclearSpaceStd.seminormFamily_isNuclearMap (E := E) n with ⟨hpmono, m, hnm, hNuc⟩
  -- `hpmono` is definitional equal to `seminormFamily_mono`, but we keep it explicit to avoid
  -- rewriting in downstream terms.
  refine ⟨m, hnm, ?_⟩
  -- The map is definitionaly the same.
  simpa [NuclearSpaceStd.seminormFamily_mono] using hNuc

/-! ## Interaction of inclusions with `toBanachOfSeminorm_seminormFamily` -/

lemma inclCLM_toBanachOfSeminorm_seminormFamily {n m : ℕ} (hnm : n ≤ m) (x : E) :
    (BanachOfSeminorm.inclCLM (E := E)
        (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
        ((seminormFamily_mono (E := E)) hnm))
      (toBanachOfSeminorm_seminormFamily (E := E) m x)
      =
    toBanachOfSeminorm_seminormFamily (E := E) n x := by
  let p : Seminorm ℝ E := seminormFamily (E := E) m
  let q : Seminorm ℝ E := seminormFamily (E := E) n
  have hx :
      toBanachOfSeminorm_seminormFamily (E := E) m x =
        ((Submodule.Quotient.mk (p := seminormKer (E := E) p) x : QuotBySeminorm (E := E) p) :
            BanachOfSeminorm (E := E) p) := by
    rfl
  have hx' :
      toBanachOfSeminorm_seminormFamily (E := E) n x =
        ((Submodule.Quotient.mk (p := seminormKer (E := E) q) x : QuotBySeminorm (E := E) q) :
            BanachOfSeminorm (E := E) q) := by
    rfl
  -- Now use `BanachOfSeminorm.inclCLM_coe` and unfold the quotient inclusion on representatives.
  simp [hx, hx', p, q, BanachOfSeminorm.inclCLM_coe, QuotBySeminorm.inclCLM, QuotBySeminorm.inclₗ_mk]

/-! ## A measurable representative for `L²` elements -/

/-- A measurable version of an `L²` random variable. -/
noncomputable def L2.measurableRep
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (X : α →₂[μ] ℝ) : α → ℝ :=
  (MeasureTheory.Lp.aestronglyMeasurable X).mk X

lemma measurable_L2_measurableRep
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (X : α →₂[μ] ℝ) : Measurable (L2.measurableRep (μ := μ) X) :=
  (MeasureTheory.Lp.aestronglyMeasurable X).measurable_mk

lemma L2_measurableRep_ae_eq
    {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}
    (X : α →₂[μ] ℝ) :
    (L2.measurableRep (μ := μ) X) =ᵐ[μ] fun a => (X a : ℝ) := by
  -- `AEStronglyMeasurable.ae_eq_mk` gives the reverse direction.
  simpa [L2.measurableRep] using (MeasureTheory.Lp.aestronglyMeasurable X).ae_eq_mk.symm

/-! ## Almost sure summability of the nuclear series (norm control) -/

section NuclearSeries

variable (T : E →ₗ[ℝ] H)

-- Notation for the ambient probability space.
local notation "Ω" => (E → ℝ)
local notation "μ" => μ[T]
-- Use a different name than `L2` to avoid clashing with the namespace `L2`.
local notation "L2Space" => (Ω →₂[μ] ℝ)

-- We fix a seminorm domination of `‖T ·‖`, then a nuclear inclusion index.
variable {n : ℕ} {C : ℝ≥0}
variable (hle : (normSeminorm ℝ H).comp T ≤ C • seminormFamily (E := E) n)
variable {m : ℕ} (hnm : n < m)

local notation "BanachN" => BanachOfSeminorm (E := E) (seminormFamily (E := E) n)
local notation "BanachM" => BanachOfSeminorm (E := E) (seminormFamily (E := E) m)

noncomputable
def evalL2BanachN : BanachN →L[ℝ] L2Space :=
  evalL2BanachCLM (E := E) (H := H) T n C hle

noncomputable
def inclBanachMN : BanachM →L[ℝ] BanachN :=
  BanachOfSeminorm.inclCLM (E := E)
    (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
    ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm))

noncomputable
def evalL2BanachM : BanachM →L[ℝ] L2Space :=
  (evalL2BanachN (T := T) (hle := hle)).comp (inclBanachMN (E := E) (n := n) (m := m) hnm)

lemma evalL2BanachM_toBanach (f : E) :
    evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m)
        (toBanachOfSeminorm_seminormFamily (E := E) m f)
      = evalL2 (E := E) (H := H) T f := by
  have hincl :
      inclBanachMN (E := E) (n := n) (m := m) hnm
          (toBanachOfSeminorm_seminormFamily (E := E) m f)
        =
      toBanachOfSeminorm_seminormFamily (E := E) n f := by
    simpa [inclBanachMN] using
      (inclCLM_toBanachOfSeminorm_seminormFamily (E := E) (n := n) (m := m)
        (Nat.le_of_lt hnm) f)
  simp [evalL2BanachM, evalL2BanachN, hincl,
    evalL2BanachCLM_toBanach (E := E) (H := H) (T := T) (n := n) (C := C) (hle := hle)]

theorem evalL2BanachM_isNuclearMap
    (hNuc :
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E)
          (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
          ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm)))) :
    IsNuclearMap (evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m)) := by
  simpa [evalL2BanachM, evalL2BanachN, inclBanachMN] using
    (IsNuclearMap.comp_left (T := (inclBanachMN (E := E) (n := n) (m := m) hnm)) hNuc
      (evalL2BanachN (E := E) (H := H) (T := T) (n := n) (C := C) (hle := hle)))

end NuclearSeries

/-! ## Extracting a nuclear series representation -/

section NuclearDecomposition

variable (T : E →ₗ[ℝ] H)

local notation "Ω" => (E → ℝ)
local notation "μ" => μ[T]
local notation "L2" => (Ω →₂[μ] ℝ)

variable {n : ℕ} {C : ℝ≥0}
variable (hle : (normSeminorm ℝ H).comp T ≤ C • seminormFamily (E := E) n)
variable {m : ℕ} (hnm : n < m)

local notation "BanachN" => BanachOfSeminorm (E := E) (seminormFamily (E := E) n)
local notation "BanachM" => BanachOfSeminorm (E := E) (seminormFamily (E := E) m)

noncomputable
def nuclearEvalL2 (x : BanachM) : L2 :=
  evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m) x

theorem isNuclearMap_nuclearEvalL2
    (hNuc :
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E)
          (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
          ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm)))) :
    IsNuclearMap
      (evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m)) := by
  exact evalL2BanachM_isNuclearMap (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm hNuc

/-- A chosen nuclear series representation for the `L²` evaluation operator on `Banach_m`. -/
theorem exists_nuclear_rep_evalL2BanachM
    (hNuc :
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E)
          (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
          ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm)))) :
    ∃ (φ : ℕ → (BanachM →L[ℝ] ℝ)) (y : ℕ → L2),
      Summable (fun k => ‖φ k‖ * ‖y k‖) ∧
        ∀ x, (evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m)) x
              = ∑' k, (φ k x) • y k := by
  simpa [IsNuclearMap] using
    (isNuclearMap_nuclearEvalL2 (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m) hNuc)

end NuclearDecomposition

/-!
## A measurable modification from the nuclear series

From the nuclear representation of the `L²` evaluation operator on a suitable local Banach space,
we build a measurable map `ω' : (E → ℝ) → (E → ℝ)` whose realizations are continuous linear
functionals (hence belong to `Set.range MinlosGaussianToWeakDual.toFun`).

The idea is that `ω'` has the same finite-dimensional marginals as the original sample path,
so its pushforward measure coincides with `gaussianProcess T`.
-/

section Modification

-- Notation for the ambient probability space.
local notation "Ω" => (E → ℝ)

variable (T : E →ₗ[ℝ] H)

local notation "μT" => μ[T]
-- Avoid clashing with the namespace `L2` used for `measurableRep`.
local notation "L2Space" => (Ω →₂[μT] ℝ)

variable {n : ℕ} {C : ℝ≥0}
variable (hle : (normSeminorm ℝ H).comp T ≤ C • seminormFamily (E := E) n)
variable {m : ℕ} (hnm : n < m)

local notation "BanachM" =>
  BanachOfSeminorm (E := E) (seminormFamily (E := E) m)

variable (hNuc :
  IsNuclearMap
    (BanachOfSeminorm.inclCLM (E := E)
      (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
      ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm))))

/-! ### A chosen nuclear series representation -/

private noncomputable def repφ : ℕ → (BanachM →L[ℝ] ℝ) :=
  Classical.choose
    (exists_nuclear_rep_evalL2BanachM (E := E) (H := H) (T := T)
      (n := n) (C := C) (hle := hle) (m := m) (hnm := hnm) hNuc)

private noncomputable def repY : ℕ → L2Space :=
  Classical.choose
    (Classical.choose_spec
      (exists_nuclear_rep_evalL2BanachM (E := E) (H := H) (T := T)
        (n := n) (C := C) (hle := hle) (m := m) (hnm := hnm) hNuc))

private lemma rep_summable :
    Summable (fun k => ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
      ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖) := by
  simpa [repφ, repY] using
    (Classical.choose_spec
      (Classical.choose_spec
        (exists_nuclear_rep_evalL2BanachM (E := E) (H := H) (T := T)
          (n := n) (C := C) (hle := hle) (m := m) (hnm := hnm) hNuc))).1

private lemma rep_evalL2BanachM_eq (x : BanachM) :
    evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m) x
      = ∑' k,
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) := by
  simpa [repφ, repY] using
    (Classical.choose_spec
      (Classical.choose_spec
        (exists_nuclear_rep_evalL2BanachM (E := E) (H := H) (T := T)
          (n := n) (C := C) (hle := hle) (m := m) (hnm := hnm) hNuc))).2 x

private noncomputable def repYfun (k : ℕ) : Ω → ℝ :=
  L2.measurableRep (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)

/-! ### The (coordinatewise) measurable modification `ω'` -/

private noncomputable def partialSum (f : E) (N : ℕ) : Ω → ℝ := fun ω =>
  ∑ k ∈ Finset.range N,
    (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
        (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
      repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω

noncomputable
def omegaMod : Ω → Ω := fun ω =>
  fun f : E => limUnder atTop (fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω)

private lemma measurable_partialSum (f : E) (N : ℕ) :
    Measurable (partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N) := by
  have hf :
      ∀ k ∈ Finset.range N,
        Measurable fun ω : Ω =>
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
              (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
            repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω := by
    intro k hk
    have hmeas : Measurable (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) := by
      simpa [repYfun] using
        (measurable_L2_measurableRep
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
    simpa [mul_assoc] using (measurable_const.mul hmeas)
  simpa [partialSum] using
    (Finset.measurable_fun_sum (s := Finset.range N)
      (f := fun k (ω : Ω) =>
        (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
            (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
          repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) hf)

@[measurability]
theorem measurable_omegaMod :
    Measurable (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) := by
  refine measurable_pi_lambda _ (fun f => ?_)
  -- Use the `StronglyMeasurable.limUnder` lemma from Mathlib (Polish/complete-metrizable targets),
  -- then convert to `Measurable`.
  have hstrong :
      MeasureTheory.StronglyMeasurable (fun ω : Ω =>
        limUnder atTop (fun N : ℕ =>
          partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω)) := by
    refine MeasureTheory.StronglyMeasurable.limUnder (ι := ℕ) (X := Ω) (E := ℝ)
      (l := (atTop : Filter ℕ))
      (f := fun N => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N) ?_
    intro N
    exact (measurable_partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N).stronglyMeasurable
  simpa [omegaMod] using hstrong.measurable

/-! ### Core API for `omegaMod` -/

@[measurability]
theorem aemeasurable_omegaMod :
    AEMeasurable (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT :=
  (measurable_omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)).aemeasurable

/-! ### Almost sure membership in `Set.range MinlosGaussianToWeakDual.toFun` -/

open scoped Topology

private noncomputable def termCLM (ω : Ω) (k : ℕ) : BanachM →L[ℝ] ℝ :=
  (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) •
    (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)

private noncomputable def LBanach (ω : Ω) : BanachM →L[ℝ] ℝ :=
  ∑' k, termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k

/-!
### A measurable `WeakDual`-valued modification

To avoid measurability issues for `Set.range MinlosGaussianToWeakDual.toFun` inside the large product
σ-algebra on `Ω = E → ℝ`, we build directly a **measurable** modification with values in
`WeakDual ℝ E` by taking the `limUnder` of the Banach-valued partial sums and then composing with
evaluation at `toBanachOfSeminorm_seminormFamily`.
-/

private noncomputable def partialSumCLM (N : ℕ) : Ω → BanachM →L[ℝ] ℝ := fun ω =>
  ∑ k ∈ Finset.range N, termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k

private lemma stronglyMeasurable_partialSumCLM (N : ℕ) :
    MeasureTheory.StronglyMeasurable (partialSumCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N) := by
  -- Each term is a product of a measurable scalar and a constant vector in a normed space.
  have hterm (k : ℕ) :
      MeasureTheory.StronglyMeasurable fun ω : Ω =>
        termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k := by
    -- `repYfun k` is measurable (hence strongly measurable) into `ℝ`.
    have hrepY :
        MeasureTheory.StronglyMeasurable
          (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) := by
      have : Measurable (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) := by
        simpa [repYfun] using
          (measurable_L2_measurableRep
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
      simpa using this.stronglyMeasurable
    -- Scalar multiplication by a strongly measurable scalar preserves strong measurability.
    simpa [termCLM] using hrepY.smul (MeasureTheory.stronglyMeasurable_const :
      MeasureTheory.StronglyMeasurable fun _ : Ω =>
        (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
  -- Finite sum of strongly measurable functions.
  simpa [partialSumCLM] using
    (Finset.stronglyMeasurable_fun_sum (s := Finset.range N)
      (f := fun k (ω : Ω) =>
        termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
      (fun k _ => hterm k))

private noncomputable def LBanachLim : Ω → BanachM →L[ℝ] ℝ := fun ω =>
  limUnder atTop (fun N : ℕ =>
    partialSumCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω)

-- Help typeclass inference: `BanachM →L[ℝ] ℝ` is completely metrizable.
open scoped Uniformity in
local instance : TopologicalSpace.IsCompletelyMetrizableSpace (BanachM →L[ℝ] ℝ) := by
  classical
  -- Use the uniform-space criterion: complete + countably generated uniformity + T0.
  letI : CompleteSpace (BanachM →L[ℝ] ℝ) := inferInstance
  letI : IsCountablyGenerated (𝓤 (BanachM →L[ℝ] ℝ)) := inferInstance
  letI : T0Space (BanachM →L[ℝ] ℝ) := inferInstance
  exact TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable

private lemma stronglyMeasurable_LBanachLim :
    MeasureTheory.StronglyMeasurable (LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) := by
  -- Strong measurability of `limUnder` holds in completely metrizable spaces, without separability assumptions.
  simpa [LBanachLim] using
    (MeasureTheory.StronglyMeasurable.limUnder (l := (atTop : Filter ℕ))
      (f := fun N : ℕ => partialSumCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N)
      (fun N => stronglyMeasurable_partialSumCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N))

@[measurability]
private lemma measurable_LBanachLim :
    Measurable (LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) := by
  simpa using (stronglyMeasurable_LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)).measurable

private noncomputable def toWeakDual (L : BanachM →L[ℝ] ℝ) : WeakDual ℝ E :=
  let toBanachLM : E →ₗ[ℝ] BanachM :=
    { toFun := toBanachOfSeminorm_seminormFamily (E := E) m
      map_add' := by
        intro x y
        simp [toBanachOfSeminorm_seminormFamily]
      map_smul' := by
        intro c x
        simp [toBanachOfSeminorm_seminormFamily] }
  let Lω : E →ₗ[ℝ] ℝ := (L.toLinearMap).comp toBanachLM
  have hle_seminorm :
      (normSeminorm ℝ ℝ).comp Lω ≤ ‖L‖₊ • seminormFamily (E := E) m := by
    intro f
    have hop :
        ‖Lω f‖ ≤ ‖L‖ * ‖toBanachOfSeminorm_seminormFamily (E := E) m f‖ := by
      simpa [Lω, toBanachLM] using (L.le_opNorm (toBanachOfSeminorm_seminormFamily (E := E) m f))
    have hnorm :
        ‖toBanachOfSeminorm_seminormFamily (E := E) m f‖ = seminormFamily (E := E) m f := by
      simpa using (norm_toBanachOfSeminorm_seminormFamily (E := E) (n := m) f)
    have hreal :
        ‖Lω f‖ ≤ (‖L‖₊ : ℝ) * seminormFamily (E := E) m f := by
      have : ‖Lω f‖ ≤ ‖L‖ * seminormFamily (E := E) m f := by
        simpa [hnorm] using hop
      simpa using this
    simpa [Seminorm.comp_apply, Seminorm.smul_apply, smul_eq_mul] using hreal
  (⟨Lω, MinlosGaussianToWeakDual.continuous_of_le_seminormFamily (E := E) (L := Lω) (n := m)
    (C := ‖L‖₊) hle_seminorm⟩ : WeakDual ℝ E)

private lemma continuous_toWeakDual : Continuous (toWeakDual (E := E) (m := m)) := by
  refine WeakDual.continuous_of_continuous_eval (𝕜 := ℝ) (E := E)
      (g := toWeakDual (E := E) (m := m)) ?_
  intro f
  have :
      (fun L : BanachM →L[ℝ] ℝ => (toWeakDual (E := E) (m := m) L) f) =
        fun L : BanachM →L[ℝ] ℝ => L (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
    rfl
  simpa [this] using
    (ContinuousLinearMap.continuous
      (ContinuousLinearMap.apply ℝ ℝ
        (toBanachOfSeminorm_seminormFamily (E := E) m f)))

/-- A measurable `WeakDual`-valued modification obtained from the nuclear series. -/
noncomputable def omegaModWeakDual : Ω → WeakDual ℝ E := fun ω =>
  toWeakDual (E := E) (m := m)
    (LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω)

@[measurability]
theorem measurable_omegaModWeakDual :
    Measurable (omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
      (hNuc := hNuc)) := by
  refine MinlosGaussianToWeakDual.weakDual_measurable_of_eval_measurable (E := E)
    (g := omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
      (hNuc := hNuc)) ?_
  intro f
  have hcont_toWeakDual : Continuous (toWeakDual (E := E) (m := m)) :=
    continuous_toWeakDual (E := E) (m := m)
  have hcont_eval :
      Continuous (fun L : BanachM →L[ℝ] ℝ => (toWeakDual (E := E) (m := m) L) f) :=
    (WeakDual.eval_continuous (𝕜 := ℝ) (E := E) f).comp hcont_toWeakDual
  have hmeas_eval :
      Measurable (fun L : BanachM →L[ℝ] ℝ => (toWeakDual (E := E) (m := m) L) f) :=
    hcont_eval.measurable
  -- `omegaModWeakDual` is obtained by composing `LBanachLim` with `toWeakDual`.
  simpa [omegaModWeakDual] using
    hmeas_eval.comp (measurable_LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc))

private lemma termCLM_apply (ω : Ω) (k : ℕ) (x : BanachM) :
    termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k x
      = (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
          (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) := by
  simp [termCLM, mul_comm]

private lemma partialSum_eq_sum_termCLM (f : E) (N : ℕ) (ω : Ω) :
    partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω
      = ∑ k ∈ Finset.range N,
          termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k
            (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
  simp [partialSum, termCLM_apply (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)]

private lemma lintegral_enorm_repYfun_le (k : ℕ) :
    (∫⁻ ω, ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT)
      ≤ ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ := by
  have hmeas :
      AEStronglyMeasurable (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) μT := by
    exact (measurable_L2_measurableRep
      (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)).aestronglyMeasurable
  have hLp :
      eLpNorm (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) 1 μT ≤
        eLpNorm (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) 2 μT := by
    simpa using
      (eLpNorm_le_eLpNorm_of_exponent_le (μ := μT)
        (f := repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)
        (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (hpq := by norm_num) hmeas)
  have hAE :
      (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k : Ω → ℝ)
        =ᵐ[μT] fun ω => (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω : ℝ) := by
    simpa [repYfun] using
      (L2_measurableRep_ae_eq
        (μ := μT) (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
  calc
    (∫⁻ ω, ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT)
        = eLpNorm (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) 1 μT := by
            simp [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
    _ ≤ eLpNorm (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) 2 μT := hLp
    _ = eLpNorm (fun ω => (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω : ℝ)) 2 μT := by
          simpa using (eLpNorm_congr_ae hAE)
    _ = ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ := by
          simp only [
            (Lp.enorm_def
              (f := (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
              (p := (2 : ℝ≥0∞)) (μ := μT)).symm]

private lemma tsum_lintegral_enorm_termCLM_ne_top :
    (∑' k,
        (∫⁻ ω, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT)) ≠ ∞ := by
  have hbound :
      (fun k =>
          (∫⁻ ω, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT))
        ≤ fun k => ENNReal.ofReal
          (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
            ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖) := by
    intro k
    have hterm :
        (∫⁻ ω,
              ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT)
          =
          (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ) *
            (∫⁻ ω,
                ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT) := by
      have hmeas :
          AEMeasurable (fun ω : Ω =>
            ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ) μT := by
        exact (measurable_L2_measurableRep
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)).enorm.aemeasurable
      calc
        (∫⁻ ω,
              ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT)
            = (∫⁻ ω,
                ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ *
                  ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ ∂μT) := by
                simp [termCLM, enorm_smul]
        _ = (∫⁻ ω,
                ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT) *
              ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ := by
                simpa using
                  (MeasureTheory.lintegral_mul_const'' (μ := μT)
                    (r := ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ)
                    (f := fun ω : Ω =>
                      ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ) hmeas)
        _ = (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ) *
              (∫⁻ ω,
                ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT) := by
                simp [mul_comm]
    calc
      (∫⁻ ω, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT)
          = (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ) *
              (∫⁻ ω, ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ ∂μT) := hterm
      _ ≤ (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ) *
            ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ := by
            gcongr
            exact lintegral_enorm_repYfun_le (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
      _ ≤ ENNReal.ofReal
            (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
              ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖) := by
            simp [enorm, ENNReal.ofReal_mul]
  have hsum :
      (∑' k, ENNReal.ofReal
          (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
            ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖)) ≠ ∞ :=
    (rep_summable (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)).tsum_ofReal_ne_top
  exact ne_of_lt <|
    lt_of_le_of_lt (ENNReal.tsum_le_tsum hbound) (lt_top_iff_ne_top.2 hsum)

private lemma ae_summable_termCLM :
    ∀ᵐ ω ∂μT, Summable (fun k =>
      termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k) := by
  have hmeas (k : ℕ) :
      AEMeasurable
        (fun ω : Ω =>
          ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ) μT := by
    have hrep :
        AEMeasurable (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) μT := by
      exact (measurable_L2_measurableRep
        (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)).aemeasurable
    have hrep_enorm :
        AEMeasurable (fun ω : Ω =>
          ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ) μT :=
      hrep.enorm
    have hprod :
        AEMeasurable (fun ω : Ω =>
          ‖repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω‖ₑ *
            ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ₑ) μT :=
      hrep_enorm.mul aemeasurable_const
    simpa [termCLM, enorm_smul] using hprod
  have h_lintegral :
      (∫⁻ ω, (∑' k, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ) ∂μT) ≠ ∞ := by
    have htonelli :
        (∫⁻ ω, (∑' k, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ) ∂μT)
          = ∑' k, (∫⁻ ω, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ ∂μT) := by
      simpa using (lintegral_tsum (fun k => hmeas k))
    simpa [htonelli] using
      tsum_lintegral_enorm_termCLM_ne_top (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)
  have hAE_lt :
      ∀ᵐ ω ∂μT,
        (∑' k, ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖ₑ) < ∞ := by
    exact
      MeasureTheory.ae_lt_top'
        (AEMeasurable.ennreal_tsum (fun k => hmeas k)) h_lintegral
  filter_upwards [hAE_lt] with ω hω
  have hω_ne :
      (∑' k, (‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖₊ : ℝ≥0∞)) ≠ ∞ := by
    simpa [enorm_eq_nnnorm] using (lt_top_iff_ne_top).1 hω
  have hnnnorm :
      Summable (fun k =>
        ‖termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k‖₊) :=
    (ENNReal.tsum_coe_ne_top_iff_summable.1 hω_ne)
  exact (Summable.of_nnnorm hnnnorm)

theorem ae_omegaMod_mem_range_toFun :
    ∀ᵐ ω ∂μT,
      omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω
        ∈ Set.range (MinlosGaussianToWeakDual.toFun (E := E)) := by
  -- A linear map `E →ₗ BanachM` corresponding to `toBanachOfSeminorm_seminormFamily m`.
  let toBanachLM : E →ₗ[ℝ] BanachM :=
    { toFun := toBanachOfSeminorm_seminormFamily (E := E) m
      map_add' := by
        intro x y
        simp [toBanachOfSeminorm_seminormFamily]
      map_smul' := by
        intro c x
        simp [toBanachOfSeminorm_seminormFamily] }
  filter_upwards [ae_summable_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)]
    with ω hω
  -- Define the Banach-space functional by summing the operator-norm summable series.
  let LωB : BanachM →L[ℝ] ℝ := LBanach (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω
  let Lω : E →ₗ[ℝ] ℝ := (LωB.toLinearMap).comp toBanachLM
  have h_tendsto :
      Tendsto
        (fun N : ℕ =>
          (∑ k ∈ Finset.range N,
              termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
        atTop (nhds LωB) := by
    simpa [LωB, LBanach] using (hω.hasSum.tendsto_sum_nat)
  have h_eval (f : E) :
      omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f
        = LωB (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
    have h_tendsto_eval :
        Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N,
              (termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
                (toBanachOfSeminorm_seminormFamily (E := E) m f))
          atTop (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
      have ht :
          Tendsto
            (fun N : ℕ =>
              (ContinuousLinearMap.apply ℝ ℝ
                  (toBanachOfSeminorm_seminormFamily (E := E) m f))
                (∑ k ∈ Finset.range N,
                  termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
            atTop
              (nhds
                ((ContinuousLinearMap.apply ℝ ℝ
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) LωB)) :=
        (((ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ
              (toBanachOfSeminorm_seminormFamily (E := E) m f))).tendsto LωB).comp h_tendsto)
      simpa using ht
    have hrewrite :
        (fun N : ℕ =>
            ∑ k ∈ Finset.range N,
              (termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
                (toBanachOfSeminorm_seminormFamily (E := E) m f))
          = fun N : ℕ =>
              partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω := by
      funext N
      simpa using
        (partialSum_eq_sum_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)
          (m := m) f N ω).symm
    have hlim : Tendsto (fun N : ℕ =>
        partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω) atTop
          (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
      simpa [hrewrite] using h_tendsto_eval
    simpa [omegaMod] using (Filter.Tendsto.limUnder_eq hlim)
  have hle_seminorm :
      (normSeminorm ℝ ℝ).comp Lω ≤ ‖LωB‖₊ • seminormFamily (E := E) m := by
    intro f
    have hop :
        ‖Lω f‖ ≤ ‖LωB‖ * ‖toBanachOfSeminorm_seminormFamily (E := E) m f‖ := by
      simpa [Lω, toBanachLM] using (LωB.le_opNorm (toBanachOfSeminorm_seminormFamily (E := E) m f))
    have hnorm :
        ‖toBanachOfSeminorm_seminormFamily (E := E) m f‖ = seminormFamily (E := E) m f := by
      simpa using (norm_toBanachOfSeminorm_seminormFamily (E := E) (n := m) f)
    have hreal :
        ‖Lω f‖ ≤ (‖LωB‖₊ : ℝ) * seminormFamily (E := E) m f := by
      have : ‖Lω f‖ ≤ ‖LωB‖ * seminormFamily (E := E) m f := by
        simpa [hnorm] using hop
      simpa using this
    simpa [Seminorm.comp_apply, Seminorm.smul_apply, smul_eq_mul] using hreal
  have hωeq : (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω)
      = fun f : E => Lω f := by
    funext f
    simpa [Lω, toBanachLM] using (h_eval f)
  have : (fun f : E => Lω f) ∈ Set.range (MinlosGaussianToWeakDual.toFun (E := E)) :=
    MinlosGaussianToWeakDual.mem_range_toFun_of_linearMap_of_le_seminormFamily (E := E)
      (L := Lω) (n := m) (C := ‖LωB‖₊) hle_seminorm
  simpa [hωeq] using this

theorem ae_exists_weakDual_toFun_eq_omegaMod :
    ∀ᵐ ω ∂μT,
      ∃ L : WeakDual ℝ E,
        MinlosGaussianToWeakDual.toFun (E := E) L
          = omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω := by
  simpa [Set.mem_range] using
    (ae_omegaMod_mem_range_toFun (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
      (hNuc := hNuc))

/-!
### `omegaMod` has the same finite-dimensional marginals

The idea is that `omegaMod` is a **modification** of the coordinate process: for each fixed
`f : E`, we have `omegaMod ω f = ω f` almost surely. This implies that `μ[T].map omegaMod = μ[T]`
by uniqueness on cylinder sets (finite-dimensional marginals).
-/

private lemma ae_tendsto_partialSum_omegaMod (f : E) :
    ∀ᵐ ω ∂μT,
      Tendsto
        (fun N : ℕ =>
          partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω)
        atTop
        (nhds (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f)) := by
  filter_upwards [ae_summable_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)]
    with ω hω
  -- Define the Banach-space functional by summing the operator-norm summable series.
  let LωB : BanachM →L[ℝ] ℝ := LBanach (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω
  have h_tendsto :
      Tendsto
        (fun N : ℕ =>
          (∑ k ∈ Finset.range N,
              termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
        atTop (nhds LωB) := by
    simpa [LωB, LBanach] using (hω.hasSum.tendsto_sum_nat)
  have h_tendsto_eval :
      Tendsto
        (fun N : ℕ =>
          ∑ k ∈ Finset.range N,
            (termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
              (toBanachOfSeminorm_seminormFamily (E := E) m f))
        atTop
          (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
    have ht :
        Tendsto
          (fun N : ℕ =>
            (ContinuousLinearMap.apply ℝ ℝ
                (toBanachOfSeminorm_seminormFamily (E := E) m f))
              (∑ k ∈ Finset.range N,
                termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
          atTop
            (nhds
              ((ContinuousLinearMap.apply ℝ ℝ
                  (toBanachOfSeminorm_seminormFamily (E := E) m f)) LωB)) :=
      (((ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ
            (toBanachOfSeminorm_seminormFamily (E := E) m f))).tendsto LωB).comp h_tendsto)
    simpa using ht
  have hlim :
      Tendsto
        (fun N : ℕ =>
          partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω)
        atTop
        (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
    simpa [partialSum_eq_sum_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) (m := m)]
      using h_tendsto_eval
  have hωeq :
      omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f
        = LωB (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
    simpa [omegaMod] using (Filter.Tendsto.limUnder_eq hlim)
  simpa [hωeq] using hlim

private lemma tendstoInMeasure_partialSum_omegaMod (f : E) :
    MeasureTheory.TendstoInMeasure μT
      (fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N)
      atTop
      (fun ω : Ω => omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f) := by
  refine MeasureTheory.tendstoInMeasure_of_tendsto_ae (μ := μT)
    (f := fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N)
    (g := fun ω : Ω => omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f) ?_ ?_
  · intro N
    exact (measurable_partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N).aestronglyMeasurable
  · simpa using (ae_tendsto_partialSum_omegaMod (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f)

private lemma coeFn_sum_range_smul_ae_eq (x : BanachM) (N : ℕ) :
    ((∑ k ∈ Finset.range N,
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) : L2Space) : Ω → ℝ)
      =ᵐ[μT]
        (fun ω : Ω =>
          ∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)) := by
  induction N with
  | zero =>
    simpa using (Lp.coeFn_zero (E := ℝ) (p := (2 : ℝ≥0∞)) (μ := μT))
  | succ N ih =>
    let A : L2Space :=
      ∑ k ∈ Finset.range N,
        (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)
    let B : L2Space :=
      (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N x) •
        (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N)
    have hAB :
        (∑ k ∈ Finset.range (N + 1),
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) : L2Space) =
          A + B := by
      simpa [A, B] using
        (Finset.sum_range_succ
          (fun k =>
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)) N)
    have h_add :
        ((∑ k ∈ Finset.range (N + 1),
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) : L2Space) : Ω → ℝ)
          =ᵐ[μT] fun ω : Ω => A ω + B ω := by
      simpa [hAB] using (Lp.coeFn_add (μ := μT) A B)
    have hB :
        (B : Ω → ℝ) =ᵐ[μT] fun ω : Ω =>
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N x) *
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω) := by
      simpa [B, smul_eq_mul] using
        (Lp.coeFn_smul (μ := μT)
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N x)
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N))
    have hA :
        (A : Ω → ℝ) =ᵐ[μT] fun ω : Ω =>
          ∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) := by
      -- induction hypothesis, rewritten with `A`.
      simpa [A] using ih
    have h_sum : (fun ω : Ω => A ω + B ω)
        =ᵐ[μT] fun ω : Ω =>
          (∑ k ∈ Finset.range N,
                (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
                  (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω))
            + (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N x) *
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω) := by
      exact hA.add hB
    have h_rw :
        (fun ω : Ω =>
            (∑ k ∈ Finset.range N,
                  (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
                    (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω))
              + (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N x) *
                  (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω))
          = fun ω : Ω =>
              ∑ k ∈ Finset.range (N + 1),
                (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
                  (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) := by
      funext ω
      simpa using
        (Finset.sum_range_succ
          (fun k =>
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) *
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)) N).symm
    exact h_add.trans (h_sum.trans (Filter.EventuallyEq.of_eq h_rw))

private lemma partialSum_ae_eq_coeFn_sum (f : E) (N : ℕ) :
    (partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N)
      =ᵐ[μT]
        ((∑ k ∈ Finset.range N,
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                  (toBanachOfSeminorm_seminormFamily (E := E) m f)) •
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) : L2Space) : Ω → ℝ) := by
  have h_repYfun (k : ℕ) :
      (repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k : Ω → ℝ)
        =ᵐ[μT]
          fun ω : Ω => (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω : ℝ) := by
    simpa [repYfun] using
      (L2_measurableRep_ae_eq
        (μ := μT) (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
  have h_term (k : ℕ) :
      (fun ω : Ω =>
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
              (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
            repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)
        =ᵐ[μT]
          fun ω : Ω =>
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) := by
    filter_upwards [h_repYfun k] with ω hω
    simp [hω]
  have h_sum :
      (fun ω : Ω =>
          ∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
              repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)
        =ᵐ[μT]
          fun ω : Ω =>
            ∑ k ∈ Finset.range N,
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                  (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) := by
    induction N with
    | zero =>
      simp
    | succ N ih =>
      have hN' := h_term N
      have h_rw1 :
          (fun ω : Ω =>
              ∑ k ∈ Finset.range (N + 1),
                (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                  repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)
            =
          (fun ω : Ω =>
              (∑ k ∈ Finset.range N,
                    (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                        (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                      repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)
                +
                  (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N
                        (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                    repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω) := by
        funext ω
        simpa using
          (Finset.sum_range_succ
            (fun k =>
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                repYfun (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) N)
      have h_rw2 :
          (fun ω : Ω =>
              ∑ k ∈ Finset.range (N + 1),
                (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                  (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω))
            =
          (fun ω : Ω =>
              (∑ k ∈ Finset.range N,
                    (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                        (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                      (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω))
                +
                  (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N
                        (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                    (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) N ω)) := by
        funext ω
        simpa using
          (Finset.sum_range_succ
            (fun k =>
              (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
                (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω)) N)
      refine (Filter.EventuallyEq.of_eq h_rw1).trans ?_
      refine (ih.add hN').trans ?_
      exact (Filter.EventuallyEq.of_eq h_rw2).symm
  have hL2 :
      ((∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                (toBanachOfSeminorm_seminormFamily (E := E) m f)) •
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k) : L2Space) : Ω → ℝ)
        =ᵐ[μT] fun ω : Ω =>
          ∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k
                (toBanachOfSeminorm_seminormFamily (E := E) m f)) *
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k ω) :=
    coeFn_sum_range_smul_ae_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc)
      (x := toBanachOfSeminorm_seminormFamily (E := E) m f) N
  simpa [partialSum] using h_sum.trans hL2.symm

private lemma tendstoInMeasure_partialSum_eval (f : E) :
    MeasureTheory.TendstoInMeasure μT
      (fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N)
      atTop
      (fun ω : Ω => ω f) := by
  -- Work with the `L²` partial sums.
  let x : BanachM := toBanachOfSeminorm_seminormFamily (E := E) m f
  let sL2 : ℕ → L2Space := fun N =>
    ∑ k ∈ Finset.range N,
      (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
        (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)
  have hsummable :
      Summable (fun k : ℕ =>
        (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)) := by
    have hbound (k : ℕ) :
        ‖(repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)‖
          ≤ ‖x‖ *
              (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
                ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖) := by
      calc
        ‖(repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)‖
            = ‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x‖ *
                ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ := by
                  simp [norm_smul]
        _ ≤ (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ * ‖x‖) *
                ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ := by
              gcongr
              simpa using (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k).le_opNorm x
        _ = ‖x‖ *
              (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
                ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖) := by
              ring_nf
    have hg :
        Summable (fun k : ℕ =>
          ‖x‖ *
            (‖repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖ *
              ‖repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k‖)) :=
      (rep_summable (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)).mul_left ‖x‖
    exact (Summable.of_norm_bounded hg hbound)
  have h_tendsto_L2 :
      Tendsto sL2 atTop (nhds (evalL2 (E := E) (H := H) T f)) := by
    have h_has : HasSum (fun k : ℕ =>
        (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
          (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
        (∑' k,
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k)) :=
      hsummable.hasSum
    have hsum_eval :
        (∑' k,
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
          = evalL2 (E := E) (H := H) T f := by
      calc
        (∑' k,
          (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
            (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
            = evalL2BanachM (E := E) (H := H) (T := T) (n := n) (C := C) hle hnm (m := m) x := by
                simpa [x] using
                  (rep_evalL2BanachM_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) x).symm
        _ = evalL2 (E := E) (H := H) T f := by
              simpa [x] using
                (evalL2BanachM_toBanach (E := E) (H := H) (T := T) (n := n) (C := C)
                  (hle := hle) (hnm := hnm) (m := m) f)
    have h_tendsto' :
        Tendsto (fun N : ℕ =>
          ∑ k ∈ Finset.range N,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))
          atTop
          (nhds (∑' k,
            (repφ (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k x) •
              (repY (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) k))) :=
      h_has.tendsto_sum_nat
    simpa [sL2, hsum_eval] using h_tendsto'
  have h_inMeas_sL2 :
      MeasureTheory.TendstoInMeasure μT (fun N : ℕ => (sL2 N : Ω → ℝ)) atTop
        (evalL2 (E := E) (H := H) T f : Ω → ℝ) :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp (μ := μT) (p := (2 : ℝ≥0∞)) h_tendsto_L2)
  have h_congr_left :
      MeasureTheory.TendstoInMeasure μT
        (fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N)
        atTop (evalL2 (E := E) (H := H) T f : Ω → ℝ) := by
    refine MeasureTheory.TendstoInMeasure.congr_left (μ := μT)
      (f := fun N : ℕ => (sL2 N : Ω → ℝ))
      (f' := fun N : ℕ => partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N) ?_
      h_inMeas_sL2
    intro N
    simpa [sL2, x] using
      (partialSum_ae_eq_coeFn_sum (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f N).symm
  exact MeasureTheory.TendstoInMeasure.congr_right (μ := μT)
    (g := (evalL2 (E := E) (H := H) T f : Ω → ℝ))
    (g' := fun ω : Ω => ω f)
    (by simpa using (evalL2_ae_eq (E := E) (H := H) (T := T) (f := f)))
    h_congr_left

theorem omegaMod_eval_ae_eq (f : E) :
    (fun ω : Ω =>
        omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f)
      =ᵐ[μT] fun ω : Ω => ω f := by
  have h1 := tendstoInMeasure_partialSum_omegaMod (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f
  have h2 := tendstoInMeasure_partialSum_eval (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f
  exact MeasureTheory.tendstoInMeasure_ae_unique (μ := μT) h1 h2

theorem omegaModWeakDual_eval_ae_eq (f : E) :
    (fun ω : Ω =>
        omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
          (hNuc := hNuc) ω f)
      =ᵐ[μT] fun ω : Ω => ω f := by
  have h₁ :
      (fun ω : Ω =>
          omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
            (hNuc := hNuc) ω f)
        =ᵐ[μT]
          fun ω : Ω => omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f := by
    filter_upwards [ae_summable_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)] with ω hω
    -- Define the Banach-space functional as the sum of the (a.s.) summable series.
    let LωB : BanachM →L[ℝ] ℝ := LBanach (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω
    have h_tendsto :
        Tendsto
          (fun N : ℕ =>
            (∑ k ∈ Finset.range N,
              termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
          atTop (nhds LωB) := by
            simpa [LωB, LBanach] using (hω.hasSum.tendsto_sum_nat)
    have h_LBanachLim :
        LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω = LωB := by
      simpa [LBanachLim] using (Filter.Tendsto.limUnder_eq h_tendsto)
    have h_tendsto_eval :
        Tendsto
          (fun N : ℕ =>
            ∑ k ∈ Finset.range N,
              (termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
                (toBanachOfSeminorm_seminormFamily (E := E) m f))
          atTop (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
      have ht :
          Tendsto
            (fun N : ℕ =>
              (ContinuousLinearMap.apply ℝ ℝ
                  (toBanachOfSeminorm_seminormFamily (E := E) m f))
                (∑ k ∈ Finset.range N,
                  termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k))
            atTop
              (nhds
                ((ContinuousLinearMap.apply ℝ ℝ
                    (toBanachOfSeminorm_seminormFamily (E := E) m f)) LωB)) :=
        (((ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ
              (toBanachOfSeminorm_seminormFamily (E := E) m f))).tendsto LωB).comp h_tendsto)
      simpa using ht
    have hrewrite :
        (fun N : ℕ =>
            ∑ k ∈ Finset.range N,
              (termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω k)
                (toBanachOfSeminorm_seminormFamily (E := E) m f))
          =
          fun N : ℕ =>
            partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω := by
      funext N
      simpa using
        (partialSum_eq_sum_termCLM (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)
          (m := m) f N ω).symm
    have hlim_scalar :
        Tendsto
          (fun N : ℕ =>
            partialSum (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) f N ω)
          atTop (nhds (LωB (toBanachOfSeminorm_seminormFamily (E := E) m f))) := by
      simpa [hrewrite] using h_tendsto_eval
    have h_omegaMod :
        omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω f
          = LωB (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
      simpa [omegaMod] using (Filter.Tendsto.limUnder_eq hlim_scalar)
    have h_omegaModWeakDual :
        omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
            (hNuc := hNuc) ω f
          = LωB (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
      have :
          omegaModWeakDual (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m)
              (hNuc := hNuc) ω f
            =
            (LBanachLim (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω)
              (toBanachOfSeminorm_seminormFamily (E := E) m f) := by
        simp [omegaModWeakDual, toWeakDual]
        rfl
      simp [this, h_LBanachLim]
    simpa [h_omegaModWeakDual] using h_omegaMod.symm
  exact h₁.trans (omegaMod_eval_ae_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f)

private lemma ae_restrict_omegaMod_eq (I : Finset E) :
    (fun ω : Ω =>
        I.restrict (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω))
      =ᵐ[μT] fun ω : Ω => I.restrict ω := by
  classical
  have hI :
      ∀ i : I,
        (fun ω : Ω =>
            omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω i.1)
          =ᵐ[μT] fun ω : Ω => ω i.1 := fun i =>
    omegaMod_eval_ae_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) i.1
  have hall :
      ∀ᵐ ω ∂μT,
        ∀ i : I,
          omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc) ω i.1 = ω i.1 := by
    refine (ae_all_iff).2 ?_
    intro i
    simpa using (hI i)
  refine hall.mono ?_
  intro ω hω
  ext i
  simpa [Finset.restrict_def] using hω i

theorem map_omegaMod_eq :
    Measure.map (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT = μT := by
  let P : ∀ I : Finset E, Measure (∀ i : I, ℝ) := fun I => Measure.map I.restrict μT
  have hPμ : MeasureTheory.IsProjectiveLimit μT P := fun I => rfl
  have hPmap :
      MeasureTheory.IsProjectiveLimit
        (Measure.map (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT) P := by
    intro I
    have hmeas_restrict : Measurable (I.restrict : Ω → (∀ i : I, ℝ)) := by
      refine measurable_pi_lambda _ (fun i => ?_)
      simpa [Finset.restrict_def] using (measurable_pi_apply (i.1 : E))
    have hmap :
        Measure.map I.restrict
            (Measure.map (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT)
          =
        Measure.map (I.restrict ∘ (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc))) μT := by
      simpa using
        (Measure.map_map (μ := μT) hmeas_restrict
          (measurable_omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)))
    have hcongr :
        (I.restrict ∘ (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)))
          =ᵐ[μT] (I.restrict : Ω → (∀ i : I, ℝ)) := by
      simpa [Function.comp] using
        (ae_restrict_omegaMod_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) I)
    have :
        Measure.map (I.restrict ∘ (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc))) μT
          = Measure.map (I.restrict : Ω → (∀ i : I, ℝ)) μT :=
      Measure.map_congr hcongr
    simpa [P, hmap] using this
  haveI : ∀ I : Finset E, IsFiniteMeasure (P I) := by
    intro I
    dsimp [P]
    infer_instance
  exact MeasureTheory.IsProjectiveLimit.unique
    (μ := Measure.map (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT)
    (ν := μT) (P := P) hPmap hPμ

/-- If `Set.range MinlosGaussianToWeakDual.toFun` is measurable (e.g. from a measurable embedding),
then `gaussianProcess T` is almost surely supported on it. -/
theorem ae_mem_range_toFun_of_measurableSet_range
    (hle : (normSeminorm ℝ H).comp T ≤ C • seminormFamily (E := E) n)
    (hnm : n < m)
    (hNuc :
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E)
          (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
          ((seminormFamily_mono (E := E)) (Nat.le_of_lt hnm))))
    (h_range :
      MeasurableSet (Set.range (MinlosGaussianToWeakDual.toFun (E := E)))) :
    ∀ᵐ ω ∂μT, ω ∈ Set.range (MinlosGaussianToWeakDual.toFun (E := E)) := by
  -- Transport the a.s. range statement along `omegaMod`, then use `map_omegaMod_eq`.
  have hf :
      AEMeasurable (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT :=
    aemeasurable_omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)
  have hpush :
      ∀ᵐ ω ∂(Measure.map (omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc)) μT),
        ω ∈ Set.range (MinlosGaussianToWeakDual.toFun (E := E)) := by
    refine (MeasureTheory.ae_map_iff (μ := μT)
      (f := omegaMod (T := T) (hle := hle) (hnm := hnm) (hNuc := hNuc))
      (hf := hf) (p := fun ω : Ω => ω ∈ Set.range (MinlosGaussianToWeakDual.toFun (E := E)))
      (hp := h_range)).2 ?_
    simpa using
      (ae_omegaMod_mem_range_toFun (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm)
        (m := m) (hNuc := hNuc))
  simpa [map_omegaMod_eq (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc)] using hpush

end Modification

-- Restore the generic quotient-module topology instance for downstream modules.
attribute [instance] QuotientModule.Quotient.topologicalSpace

end MinlosGaussianSupport

end

end OSforGFF
