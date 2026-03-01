import OSforGFF.GFF.PackageOS2
import OSforGFF.GFF.PackageOS0Proved
import OSforGFF.OS1_GFF
import OSforGFF.OS2_GFF
import OSforGFF.GFFIsGaussian
import OSforGFF.GaussianFreeField

namespace OSforGFF
namespace GFF

open MeasureTheory Complex QFT

noncomputable section

/-- The proved free-field backend packaged as `GFF.PackageOS2`. -/
noncomputable def packageOS2Proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    PackageOS2 (m := m) :=
  { -- OS0 + μ + real CF
    (packageOS0Proved (m := m)) with
    -- OS1 obligation for p = 2
    twoPointIntegrable := by
      simpa using (gff_two_point_locally_integrable (m := m))
    -- OS2: obtain Euclidean invariance from Gaussianity + covariance invariance
    os2 := by
      -- Use the generic Gaussian⇒OS2 lemma.
      have h_gauss : isGaussianGJ (gaussianFreeField_free m) :=
        isGaussianGJ_gaussianFreeField_free (m := m)
      have h_cov : CovarianceEuclideanInvariantℂ (μ_GFF m) :=
        CovarianceEuclideanInvariantℂ_μ_GFF (m := m)
      -- `μ_GFF m` is definitional equal to `gaussianFreeField_free m`.
      simpa [μ_GFF] using (gaussian_satisfies_OS2 (dμ_config := gaussianFreeField_free m) h_gauss h_cov) }

end
end GFF
end OSforGFF

