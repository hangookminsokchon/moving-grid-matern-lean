import Lean.Util.CollectAxioms
import MaternAudit

#print axioms MaternAudit.Expectation.eq41_squared_error
#print axioms MaternAudit.PairCounting.eq41_finite_iid
#print axioms MaternAudit.spectral_autocorrelation_deficit
#print axioms MaternAudit.eq42_torus_bound
#print axioms MaternAudit.iid_torus_pair_le_spectral_energy
#print axioms MaternAudit.FixedGridLaw.pairMean_sq_norm_gramKernel_tendsto_ae
#print axioms MaternAudit.FixedFourier.sampleEnergy_tendsto_ae
#print axioms MaternAudit.FixedFourier.populationEnergy_le_spectral
#print axioms MaternAudit.FixedFourier.sampleEnergy_eventually_lt_spectral
#print axioms MaternAudit.OverlapVariance.sum_overlapWeight
#print axioms MaternAudit.OverlapVariance.variance_pairAverage
#print axioms MaternAudit.OverlapVariance.chebyshev_pairAverage
#print axioms MaternAudit.spectral_density_limit
#print axioms MaternAudit.DiagonalObstruction.abs_infiniteKernel_sub_kernel_le
#print axioms MaternAudit.DiagonalObstruction.growingGrid_counterexample

#print axioms MaternAudit.MaternParameters.omitted_eq_rescaled
#print axioms MaternAudit.MaternProfile.tendsto_shifted_energy
#print axioms MaternAudit.DesignParseval.sampled_parseval
#print axioms MaternAudit.SampleTightness.uniform_sampled_energy_tight
#print axioms MaternAudit.DesignLaw.unitCube_ae_eq_Icc
#print axioms MaternAudit.PairSpectrum.independentPair_eq_spectrum
#print axioms MaternAudit.PopulationLimit.tendsto_normalizedPairSpectrum
#print axioms MaternAudit.IIDVariance.variance_le_envelopes
#print axioms MaternAudit.MovingMatern.movingMatern_sharp
#print axioms MaternAudit.PhysicalKernel.finiteGrid_sub_kernel
#print axioms MaternAudit.FullCovariance.movingMatern_full_sharp
#print axioms MaternAudit.SpectralNormalization.integral_spectralDensity
#print axioms MaternAudit.SpectralNormalization.integrable_inverseFourier
#print axioms MaternAudit.SpectralNormalization.kernel_zero
#print axioms MaternAudit.RealCovariance.frobeniusNorm_error_eq_real
#print axioms MaternAudit.MaternBessel.kernel_eq_gammaIntegral
#print axioms MaternAudit.MaternBessel.kernel_eq_besselK
#print axioms MaternAudit.PaperTheorem.sharp_covariance_rms
#print axioms MaternAudit.TriangularRows.movingMatern_sharp_rows
#print axioms MaternAudit.TriangularRows.movingMatern_full_sharp_rows

run_cmd
  let decl := ``MaternAudit.Manuscript.sharp_matern_rows
  let actual ← Lean.collectAxioms decl
  let expected := #[``propext, ``Classical.choice, ``Quot.sound]
  unless actual.qsort Lean.Name.lt == expected.qsort Lean.Name.lt do
    throwError "unexpected axioms for {decl}: {actual.toList}"

  -- Include private lemmas by selecting theorems from each imported project module.
  let env ← Lean.getEnv
  let mut theorems := #[]
  for modName in env.header.moduleNames, modData in env.header.moduleData do
    if (`MaternAudit).isPrefixOf modName then
      for info in modData.constants do
        if let .thmInfo thm := info then
          theorems := theorems.push thm.name
  let (_, state) := ((theorems.forM Lean.CollectAxioms.collect).run env).run {}
  let unexpected := state.axioms.filter (fun ax => !expected.contains ax)
  unless unexpected.isEmpty do
    throwError "project theorems depend on unexpected axioms: {unexpected.toList}"
  Lean.logInfo m!"Checked {theorems.size} project theorem declarations against the axiom allowlist."

#print axioms MaternAudit.Manuscript.sharp_matern_rows
