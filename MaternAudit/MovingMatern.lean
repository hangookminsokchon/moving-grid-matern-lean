import MaternAudit.MatrixLimit
import MaternAudit.PairSpectrum
import MaternAudit.PopulationLimit

/-!
# Exact two-term Matérn truncation RMS on moving Fourier grids

The public theorem takes a positive smoothness, a bounded spatial probability
density, iid sample points, and the three growth conditions in `Grid`. The
coefficients in its observed statistic are the physical omitted frequencies.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace MaternAudit.MovingMatern
open MaternParameters MaternProfile PopulationLimit PairSpectrum IIDVariance
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- Observed mean of all squared Matérn Fourier-tail entries, including the diagonal. -/
def tailEnergy (g : Grid) (ν : ℝ) (X : ℕ → Ω → E d) (n : ℕ) : Ω → ℝ :=
  MatrixLimit.observed g (fun k ↦ physicalLoss (g.h k) (omitted ν (g.len k) (g.h k) (g.m k))) X n

/-- Deterministic squared equivalent in physical units. `D.designMass` is the integral of ρ². -/
def leadingSq (g : Grid) (ν : ℝ) (D : DesignLaw.Density d) (n : ℕ) : ℝ :=
  (amplitude d ν (g.len n) (g.R n))^2 *
    (I1 d (beta d ν)^2 * g.u n + (D.designMass * I2 d (beta d ν)) * g.v d n)

theorem leadingSq_pos (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) (n : ℕ) : 0 < leadingSq g ν D n := by
  have hβ : (d : ℝ) < beta d ν := by unfold beta; linarith
  have hc := cInfinity_pos (d := d) hν
  have hlen := g.len_pos n
  have hR := g.R_pos n
  have h1 := I1_pos hd hβ
  have h2 := I2_pos hd hβ
  have hmass := D.designMass_pos
  have hu := g.u_pos n
  have hv := g.v_pos d n
  unfold leadingSq amplitude
  positivity

omit [MeasurableSpace Ω] in
/-- The displayed entrywise meaning of the observed squared RMS. -/
theorem tailEnergy_eq_frobenius (g : Grid) (ν : ℝ) (X : ℕ → Ω → E d) (n : ℕ) (ω : Ω) :
    tailEnergy g ν X n ω =
      (∑ i : Fin (g.N n), ∑ j : Fin (g.N n),
        ‖FixedGridLaw.gramKernel (omitted ν (g.len n) (g.h n) (g.m n))
          (physicalFeature (g.h n)) (X i ω) (X j ω)‖^2) / (g.N n : ℝ)^2 := by
  unfold tailEnergy MatrixLimit.observed statistic OverlapVariance.pairAverage physicalLoss
  ring

/-- Both sharp equivalents for arbitrary deterministic moving grids and iid designs.
There is no restriction on the relative growth of sample size and cutoff volume. -/
theorem movingMatern_sharp (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E d} (hx : SampleLaw P D.μ X) :
    Tendsto (fun n ↦ (∫ ω, tailEnergy g ν X n ω ∂P) / leadingSq g ν D n) atTop (𝓝 1) ∧
    ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real {ω |
      ε ≤ |Real.sqrt (tailEnergy g ν X n ω) / Real.sqrt (leadingSq g ν D n) - 1|}) atTop (𝓝 0) := by
  let A := I1 d (beta d ν)^2
  let B := D.designMass * I2 d (beta d ν)
  let δ (n : ℕ) := (∑' j : Z d, coeff g ν n j)^2
  let H (n : ℕ) := physicalLoss (g.h n) (coeff (d := d) g ν n)
  have hβ : (d : ℝ) < beta d ν := by unfold beta; linarith
  have hA : 0 < A := sq_pos_of_pos (I1_pos hd hβ)
  have hI2 := I2_pos hd hβ
  have hB : 0 < B := mul_pos D.designMass_pos hI2
  have hBd (n : ℕ) : KernelBounds (H n) (δ n) (δ n) :=
    kernelBounds (g.h n) (coeff_nonneg g ν n) (summable_coeff g hν n)
  have hdiag : Tendsto δ atTop (𝓝 A) := (tendsto_coeff_mass g hν).pow 2
  have hpair : Tendsto (fun n ↦ (∫ z, Function.uncurry (H n) z ∂D.μ.prod D.μ) / g.v d n)
      atTop (𝓝 B) := by
    refine (tendsto_normalizedPairSpectrum g hν D.integrable D.memLp_two D.support).congr fun n ↦ ?_
    change normalizedPairSpectrum g ν D.ρ n =
      (∫ p : E d × E d, physicalLoss (g.h n) (coeff g ν n) p.1 p.2 ∂D.μ.prod D.μ) / g.v d n
    rw [independentPair_eq_spectrum (g.h n) D (summable_abs_coeff g hν n)]
    have hf (r : Z d) : DesignParseval.sampleFreq (g.h n) 0 r = frequency g n r := by
      funext i
      simp [DesignParseval.sampleFreq, frequency]
    simp only [normalizedPairSpectrum, hf, Grid.v, div_inv_eq_mul]
    exact mul_comm _ _
  have hproj : ∃ C ≥ (0 : ℝ), ∀ᶠ n in atTop, ∀ᵐ x ∂D.μ,
      projection D.μ (H n) x ≤ C * g.v d n := by
    refine ⟨(D.L : ℝ) * (I2 d (beta d ν) + 1), mul_nonneg D.L.coe_nonneg (by linarith), ?_⟩
    filter_upwards [(tendsto_coeff_energy g (d := d) hν).eventually_le_const
      (lt_add_one (I2 d (beta d ν)))] with n hn
    rw [div_le_iff₀ (g.v_pos d n)] at hn
    apply ae_of_all
    intro x
    have hp := conditionalRow_le D (g.h_pos n) (g.h_le_one n) (summable_abs_coeff g hν n) x
    calc
      projection D.μ (H n) x ≤ _ := hp
      _ = (D.L : ℝ) * (((g.h n)^d)⁻¹ * ∑' j : Z d, coeff g ν n j ^ 2) := by ring
      _ ≤ (D.L : ℝ) * ((I2 d (beta d ν)+1) * g.v d n) :=
        mul_le_mul_of_nonneg_left hn D.L.coe_nonneg
      _ = _ := by ring
  obtain ⟨hmean, hrms⟩ := MatrixLimit.two_term_matrix hx g d H δ A B hA hB hBd hdiag hpair hproj
  let a n := amplitude d ν (g.len n) (g.R n)
  have ha (n : ℕ) : 0 < a n := mul_pos (cInfinity_pos hν)
    (Real.rpow_pos_of_pos (mul_pos (g.len_pos n) (g.R_pos n)) _)
  have hs (n : ℕ) : 0 < A * g.u n + B * g.v d n :=
    add_pos (mul_pos hA (g.u_pos n)) (mul_pos hB (g.v_pos d n))
  apply MatrixLimit.restore_amplitude (MatrixLimit.observed g H X) (tailEnergy g ν X) a
    (fun n ↦ A * g.u n + B * g.v d n) ha hs _ hmean hrms
  apply MatrixLimit.observed_scale
  intro n x y
  change physicalLoss (g.h n) (omitted ν (g.len n) (g.h n) (g.m n)) x y = _
  simp_rw [funext (omitted_eq_amplitude_mul_coeff (d := d) g ν n)]
  exact physicalLoss_mul _ _ _ _ _

end MaternAudit.MovingMatern
