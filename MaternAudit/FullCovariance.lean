import MaternAudit.MovingMatern
import MaternAudit.PhysicalKernel
import MaternAudit.AliasTransfer

/-! The two sharp limits for the actual finite Fourier matrix minus the
continuous Matérn matrix under negligible uniform aliasing. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology
namespace MaternAudit.FullCovariance
open MaternParameters MaternProfile MovingMatern PairSpectrum PopulationLimit
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The rate without the fixed positive density and spectral constants. -/
def baseRate (d : ℕ) (ν : ℝ) (g : Grid) (n : ℕ) :=
  (g.len n * g.R n)^(-2 * ν) * Real.sqrt (g.u n + g.v d n)

/-- Entrywise error of the finite approximation, with the exact covariance
defined by the inverse Fourier integral of its physical spectral density. -/
def errorMatrix (g : Grid) (ν : ℝ) (X : ℕ → Ω → E d) (n : ℕ) (ω : Ω) :
    Matrix (Fin (g.N n)) (Fin (g.N n)) ℂ := fun i j ↦
  PhysicalKernel.finiteGrid ν (g.len n) (g.h n) (g.m n) (X i ω) (X j ω) -
    PhysicalKernel.kernel ν (g.len n) (X i ω - X j ω)

def fullRMS (g : Grid) (ν : ℝ) (X : ℕ → Ω → E d) (n : ℕ) (ω : Ω) :=
  AliasTransfer.sampleRMS (errorMatrix g ν X n ω)

private theorem alias_negligible {ν : ℝ} (hd : 0 < d) (hν : 0 < ν)
    (g : Grid) (D : DesignLaw.Density d) (η : ℕ → ℝ) (hη : ∀ n, 0 ≤ η n)
    (hsmall : Tendsto (fun n ↦ η n / baseRate d ν g n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ η n / Real.sqrt (leadingSq g ν D n)) atTop (𝓝 0) := by
  let A := I1 d (beta d ν)^2
  let B := D.designMass * I2 d (beta d ν)
  have hβ : (d : ℝ) < beta d ν := by unfold beta; linarith
  have hA : 0 < A := sq_pos_of_pos (I1_pos hd hβ)
  have hB : 0 < B := mul_pos D.designMass_pos (I2_pos hd hβ)
  let C := cInfinity d ν * Real.sqrt (min A B)
  have hc := cInfinity_pos (d := d) hν
  have hmin := lt_min hA hB
  have hC : 0 < C := mul_pos hc (Real.sqrt_pos.mpr hmin)
  have hup : Tendsto (fun n ↦ (η n / baseRate d ν g n) / C) atTop (𝓝 0) := by
    simpa using hsmall.div_const C
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
  · intro n
    exact div_nonneg (hη n) (Real.sqrt_nonneg _)
  intro n
  have hp : 0 < (g.len n * g.R n)^(-2 * ν) :=
    Real.rpow_pos_of_pos (mul_pos (g.len_pos n) (g.R_pos n)) _
  have hbr : 0 < baseRate d ν g n :=
    mul_pos hp (Real.sqrt_pos.mpr (add_pos (g.u_pos n) (g.v_pos d n)))
  have hcompare : min A B * (g.u n + g.v d n) ≤ A * g.u n + B * g.v d n := by
    rw [mul_add]
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_left _ _) (g.u_pos n).le)
      (mul_le_mul_of_nonneg_right (min_le_right _ _) (g.v_pos d n).le)
  have hlower : baseRate d ν g n * C ≤ Real.sqrt (leadingSq g ν D n) := by
    have hs := Real.sqrt_le_sqrt hcompare
    rw [Real.sqrt_mul hmin.le] at hs
    change _ ≤ Real.sqrt ((cInfinity d ν * (g.len n * g.R n)^(-2*ν))^2 *
      (A * g.u n + B * g.v d n))
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (mul_pos hc hp).le]
    dsimp only [C, baseRate]
    calc
      _ = (cInfinity d ν * (g.len n * g.R n)^(-2*ν)) *
        (Real.sqrt (min A B) * Real.sqrt (g.u n + g.v d n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hs (mul_pos hc hp).le
  change η n / Real.sqrt (leadingSq g ν D n) ≤ η n / baseRate d ν g n / C
  rw [div_div]
  exact div_le_div_of_nonneg_left (hη n) (mul_pos hbr hC) hlower

private theorem full_measurable (g : Grid) (ν : ℝ) {P : Measure Ω} (D : DesignLaw.Density d)
    {X : ℕ → Ω → E d} (hx : IIDVariance.SampleLaw P D.μ X) (n : ℕ) : Measurable (fullRMS g ν X n) := by
  have hentry (i j : Fin (g.N n)) : Measurable (fun ω ↦ errorMatrix g ν X n ω i j) := by
    let f := fun z : E d × E d ↦ PhysicalKernel.finiteGrid ν (g.len n) (g.h n) (g.m n) z.1 z.2 -
      PhysicalKernel.kernel ν (g.len n) (z.1 - z.2)
    change Measurable (f ∘ fun ω ↦ (X i ω, X j ω))
    exact (PhysicalKernel.measurable_error (d := d) ν (g.len n) (g.h n) (g.m n)).comp
      ((hx.marginal (i : ℕ)).measurable.prodMk (hx.marginal (j : ℕ)).measurable)
  change Measurable (fun ω ↦ AliasTransfer.sampleRMS (errorMatrix g ν X n ω))
  simp only [AliasTransfer.sampleRMS_eq_sqrt_mean_sq]
  exact Real.continuous_sqrt.measurable.comp ((Finset.measurable_sum _ fun i _ ↦
    Finset.measurable_sum _ fun j _ ↦ (hentry i j).norm.pow_const 2).div_const _)

/-- End-to-end result for the actual finite-grid covariance matrix error. The
alias envelope is measured on pairs of design locations, on the RMS scale. -/
theorem movingMatern_full_sharp (hd : 0 < d) {ν : ℝ} (hν : 0 < ν) (g : Grid)
    (D : DesignLaw.Density d) {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → E d} (hx : IIDVariance.SampleLaw P D.μ X)
    (η : ℕ → ℝ) (hbound : ∀ n, PhysicalKernel.AliasBound d ν (g.len n) (g.h n) (η n))
    (hsmall : Tendsto (fun n ↦ η n / baseRate d ν g n) atTop (𝓝 0)) :
    Tendsto (fun n ↦ (∫ ω, fullRMS g ν X n ω ^ 2 ∂P) / leadingSq g ν D n) atTop (𝓝 1) ∧
      ∀ ε > (0 : ℝ), Tendsto (fun n ↦ P.real {ω |
        ε ≤ |fullRMS g ν X n ω / Real.sqrt (leadingSq g ν D n) - 1|}) atTop (𝓝 0) := by
  let L n := Real.sqrt (leadingSq g ν D n)
  let T n ω := Real.sqrt (tailEnergy g ν X n ω)
  have hL (n) : 0 < L n := Real.sqrt_pos.mpr (leadingSq_pos hd hν g D n)
  have hLsq (n) : (L n)^2 = leadingSq g ν D n := Real.sq_sqrt (leadingSq_pos hd hν g D n).le
  have hη (n) : 0 ≤ η n := by
    obtain ⟨x, hxC⟩ := D.ae_mem_unitCube.exists
    exact (norm_nonneg _).trans (hbound n x hxC x hxC)
  have hsm := alias_negligible hd hν g D η hη hsmall
  have hZ (n ω) : 0 ≤ tailEnergy g ν X n ω := by
    rw [tailEnergy_eq_frobenius]
    positivity
  have hTsq (n ω) : T n ω ^ 2 = tailEnergy g ν X n ω := Real.sq_sqrt (hZ n ω)
  have hfor (n : ℕ) : ∀ᵐ ω ∂P, |fullRMS g ν X n ω - T n ω| ≤ η n := by
    have hc : ∀ᵐ ω ∂P, ∀ i : ℕ, X i ω ∈ DesignParseval.unitCube d :=
      ae_all_iff.mpr fun i ↦ (hx.marginal i).quasiMeasurePreserving.ae D.ae_mem_unitCube
    filter_upwards [hc] with ω hω
    let t : Matrix (Fin (g.N n)) (Fin (g.N n)) ℂ := fun i j ↦
      FixedGridLaw.gramKernel (omitted ν (g.len n) (g.h n) (g.m n)) (physicalFeature (g.h n)) (X i ω) (X j ω)
    let a : Matrix (Fin (g.N n)) (Fin (g.N n)) ℂ := fun i j ↦
      PhysicalKernel.alias ν (g.len n) (g.h n) (X i ω) (X j ω)
    have he : errorMatrix g ν X n ω = a - t := by
      ext i j
      exact PhysicalKernel.finiteGrid_sub_kernel hν (g.len_pos n) (g.h_pos n) (g.m n) _ _
    have ht : AliasTransfer.sampleRMS t = T n ω := by
      change AliasTransfer.sampleRMS t = Real.sqrt (tailEnergy g ν X n ω)
      rw [AliasTransfer.sampleRMS_eq_sqrt_mean_sq, tailEnergy_eq_frobenius]
    rw [fullRMS, he, ← ht]
    exact AliasTransfer.sampleRMS_alias_sub a t (hη n) (fun i j ↦ hbound n _ (hω _) _ (hω _))
  have htM (n : ℕ) : MemLp (T n) 2 P := by
    let c := omitted (d := d) ν (g.len n) (g.h n) (g.m n)
    have he : c = fun j ↦ amplitude d ν (g.len n) (g.R n) * coeff g ν n j :=
      funext (omitted_eq_amplitude_mul_coeff g ν n)
    have ha : 0 < amplitude d ν (g.len n) (g.R n) := mul_pos (cInfinity_pos hν)
      (Real.rpow_pos_of_pos (mul_pos (g.len_pos n) (g.R_pos n)) _)
    have hc₀ (j) : 0 ≤ c j := by rw [he]; exact mul_nonneg ha.le (coeff_nonneg g ν n j)
    have hcs : Summable c := he ▸ (summable_coeff g hν n).mul_left _
    have hZLp : MemLp (tailEnergy g ν X n) 2 P :=
      IIDVariance.statistic_memLp (hx.first (g.N n)) (kernelBounds (g.h n) hc₀ hcs)
    apply (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hZLp.aestronglyMeasurable)).mpr
    simpa only [Real.sq_sqrt (hZ n _)] using hZLp.integrable one_le_two
  obtain ⟨he, hp⟩ := movingMatern_sharp hd hν g D hx
  constructor
  · have hm : Tendsto (fun n ↦ (∫ ω, T n ω ^ 2 ∂P) / L n ^ 2) atTop (𝓝 1) := by
      simpa only [hTsq, hLsq] using he
    simpa only [hLsq] using AliasTransfer.secondMoment_ratio P hL htM
      (fun n ↦ (full_measurable g ν D hx n).aestronglyMeasurable) hfor hsm hm
  · exact AliasTransfer.probability_ratio P (limit := fun _ ↦ 1) hL hfor hsm hp

end MaternAudit.FullCovariance
