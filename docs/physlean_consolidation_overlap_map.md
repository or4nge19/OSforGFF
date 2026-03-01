## Overlap map: `OSforGFF` / `gaussian-field-main` → `PhysLean`

This file is a **mechanical map** of where the same concepts appear in multiple packages in this
workspace, and which file should be treated as the **canonical** source going forward.

The intended end-state is:

- `PhysLean-master/PhysLean/...` holds **small, reusable** infrastructure (σ-algebras, OS time ops,
  vector-valued Schwartz/WeakDual plumbing, minimal model containers).
- The larger developments (`OSforGFF/`, `gaussian-field-main/`, `Pphi2/`, `StochasticPDE/`, `GFF-main/`)
  remain separate Lake packages, and **depend on PhysLean** rather than duplicating it.

### Summary table

| Concept | Canonical location (PhysLean) | Current duplicates | Consolidation action |
|---|---|---|---|
| Cylindrical σ-algebra on `WeakDual` + universal property `Measurable g ↔ ∀ f, Measurable (g·f)` | `PhysLean-master/PhysLean/Mathematics/Distribution/WeakDualMeasurable.lean` | `OSforGFF/WeakDualCylindrical.lean`; ad-hoc instance in `OSforGFF/Basic.lean`; similar setup in `gaussian-field-main/GaussianField/Construction.lean` | Replace OSforGFF duplicates by imports/re-exports of PhysLean lemmas; in gaussian-field-main, either import PhysLean lemma module or prove that its instance is definitional equal to the PhysLean `comap ... pi` definition. |
| Finite-dimensional projections / cylinder generators (`weakDualProj`, `weakDualFinCylinders`) | `PhysLean-master/PhysLean/Mathematics/Distribution/WeakDualMeasurable.lean` | `OSforGFF/WeakDualCylindrical.lean` | Delete/convert duplicate file to a thin re-export. |
| Coordinate-free “time direction” (`vec`, `timeCoord`, translations, reflection ops, induced action on Schwartz maps) | `PhysLean-master/PhysLean/SpaceAndTime/SpaceTime/TimeDirection.lean` | `OSforGFF/Spacetime/TimeDirection.lean` | Replace by importing PhysLean’s `SpaceTime.TimeDirection` / `TimeDirectionOps` (keep OSforGFF file only as a re-export if needed). |
| Vector-valued Schwartz test functions + distribution spaces (`VectorTestFunction`, `WeakDual.comap`, pairing CLM, lifting internal symmetries) | `PhysLean-master/PhysLean/QFT/Euclidean/VectorValued.lean` | `OSforGFF/Spacetime/VectorValued.lean` | Replace OSforGFF duplicate by PhysLean import; keep the OSforGFF namespace only as a compatibility layer if required. |
| Minimal Euclidean QFT model container | `PhysLean-master/PhysLean/QFT/Euclidean/Model.lean` | `OSforGFF/QFT/EuclideanQFT.lean` | Replace OSforGFF’s `QFT.EuclideanQFTModel` by `PhysLean.QFT.EuclideanQFTModel` (thin alias if existing downstream code expects the old name). |
| Minimal Gel’fand triple interface (`N ⊂ H ⊂ N'` with `toHilbert`, and the canonical `H → WeakDual ℝ N` embedding) | `PhysLean-master/PhysLean/QFT/Euclidean/GelfandTriple.lean` | `OSforGFF/Minlos/GelfandTriple.lean` | Make OSforGFF extend PhysLean’s minimal structure with *additional hypotheses* (e.g. nuclearity) and Minlos/Gaussian constructions, rather than redefining the structure itself. |

### Notes (why the split matters)

- **Mathlib-facing probability results** should not be “owned by PhysLean”. In this workspace they live
  in `Common/Mathlib/...` as an upstream queue (Cameron–Martin, Fernique, Gaussian IBP). PhysLean should
  only provide stable “front door” re-exports once they land in Mathlib.
- **Field configurations**: `OSforGFF/Basic.lean` currently installs a global
  `MeasurableSpace (WeakDual ℝ (SchwartzMap SpaceTime ℝ))` instance (cylindrical). PhysLean’s design
  in `WeakDualMeasurable.lean` intentionally avoids a global instance to reduce conflicts; OSforGFF
  can keep a local/global instance *inside OSforGFF* if that is convenient, but should source the
  underlying lemmas from PhysLean.

