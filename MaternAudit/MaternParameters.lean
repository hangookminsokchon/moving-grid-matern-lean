import MaternAudit.MaternProfileBounds
import MaternAudit.MovingCells
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.FieldSimp

/-! Physical spectral parameters. Frequencies are cycles per unit length. -/

noncomputable section
open Filter
open scoped Topology
namespace MaternAudit.MaternParameters
open MaternProfile MovingCells
variable {d : ℕ}

/-- The smoothness exponent plus Euclidean dimension. -/
def beta (d : ℕ) (ν : ℝ) := 2 * ν + d

/-- High-frequency constant of the unit-variance Matérn spectral density. -/
def cInfinity (d : ℕ) (ν : ℝ) :=
  (ν / 2) ^ ν * Real.Gamma (ν + d / 2) /
    (Real.pi ^ (2 * ν + d / 2) * Real.Gamma ν)

def frequencyScale (ν ℓ : ℝ) := Real.sqrt (2 * ν) / (2 * Real.pi * ℓ)

/-- Matérn spectral density in cycles, factored using its high-frequency constant. -/
def spectralDensity (ν ℓ : ℝ) (ξ : Fin d → ℝ) : ℝ :=
  cInfinity d ν * ℓ ^ (-2 * ν) *
    (radiusSq ξ + (frequencyScale ν ℓ)^2) ^ (-beta d ν / 2)

theorem cInfinity_pos {ν : ℝ} (hν : 0 < ν) : 0 < cInfinity d ν := by
  unfold cInfinity
  positivity

/-- Physical Fourier coefficient retained in the omitted tail.
The cutoff norm on the lattice embedded in real coordinates is the maximum norm. -/
def omitted (ν ℓ h : ℝ) (m : ℕ) (j : Fin d → ℤ) : ℝ :=
  if (m : ℝ) < ‖lattice j‖ then h ^ d * spectralDensity ν ℓ (h • lattice j) else 0

theorem radiusSq_smul (R : ℝ) (x : Fin d → ℝ) : radiusSq (R • x) = R^2 * radiusSq x := by
  unfold radiusSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  change (R * x i)^2 = R^2 * x i^2
  ring

def amplitude (d : ℕ) (ν ℓ R : ℝ) := cInfinity d ν * (ℓ * R)^(-2 * ν)

/-- Exact rescaling, for every finite mesh and every integer frequency. -/
theorem omitted_eq_rescaled {ν ℓ h : ℝ} {m : ℕ} (hℓ : 0 < ℓ) (hh : 0 < h)
    (hm : 0 < m) (j : Fin d → ℤ) :
    omitted ν ℓ h m j = amplitude d ν ℓ (h * m) *
      ((m : ℝ)^d)⁻¹ * profile (beta d ν) (frequencyScale ν ℓ / (h * m)) (gridPoint m j) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  let R := h * (m : ℝ)
  have hR : 0 < R := mul_pos hh hm'
  let y := gridPoint m j
  have hy : y = (1 / (m : ℝ)) • lattice j := gridPoint_eq_smul_lattice m j
  have hξ : h • lattice j = R • y := by
    rw [hy, smul_smul]
    have hid : R * (1 / (m : ℝ)) = h := by dsimp [R]; field_simp
    rw [hid]
  have hcut : 1 < ‖y‖ ↔ (m : ℝ) < ‖lattice j‖ := by
    rw [hy, norm_smul, Real.norm_eq_abs, abs_of_pos (one_div_pos.mpr hm')]
    rw [one_div_mul_eq_div, lt_div_iff₀ hm', one_mul]
  change (if (m : ℝ) < ‖lattice j‖ then _ else _) = _ * profile _ _ y
  unfold profile
  split_ifs with hj hxy hxy
  · change h^d * spectralDensity ν ℓ (h • lattice j) = amplitude d ν ℓ R *
      ((m : ℝ)^d)⁻¹ * (radiusSq y + (frequencyScale ν ℓ / R)^2)^(-beta d ν/2)
    rw [hξ, spectralDensity, radiusSq_smul]
    have hbase : R^2 * radiusSq y + (frequencyScale ν ℓ)^2 =
        R^2 * (radiusSq y + (frequencyScale ν ℓ / R)^2) := by field_simp; ring
    rw [hbase, Real.mul_rpow (sq_nonneg R) (add_nonneg (radiusSq_nonneg y) (sq_nonneg _))]
    have hpow : (R^2)^(-beta d ν/2) = R^(-2 * ν) * (R^d)⁻¹ := by
      rw [← Real.rpow_natCast R 2, ← Real.rpow_mul hR.le]
      change R ^ ((2 : ℝ) * (-beta d ν/2)) = _
      have hex : (2 : ℝ) * (-beta d ν / 2) = -2 * ν + -(d : ℝ) := by unfold beta; ring
      rw [hex, Real.rpow_add hR, Real.rpow_neg hR.le, Real.rpow_natCast]
    rw [hpow, amplitude, Real.mul_rpow hℓ.le hR.le]
    dsimp [R]
    rw [mul_pow]
    field_simp
    ring
  · exact (hxy (hcut.mpr hj)).elim
  · exact (hj (hcut.mp hxy)).elim
  · simp

/-- Deterministic grid and length-scale sequences from the statistical statement. -/
structure Grid where
  h : ℕ → ℝ
  len : ℕ → ℝ
  m : ℕ → ℕ
  N : ℕ → ℕ
  h_pos : ∀ n, 0 < h n
  h_le_one : ∀ n, h n ≤ 1
  len_pos : ∀ n, 0 < len n
  m_pos : ∀ n, 0 < m n
  N_pos : ∀ n, 0 < N n
  radius_grows : Tendsto (fun n ↦ h n * (m n : ℝ)) atTop atTop
  scaled_radius_grows : Tendsto (fun n ↦ len n * (h n * (m n : ℝ))) atTop atTop
  sample_grows : Tendsto N atTop atTop

namespace Grid
def R (g : Grid) (n : ℕ) := g.h n * (g.m n : ℝ)
def t (g : Grid) (ν : ℝ) (n : ℕ) := frequencyScale ν (g.len n) / g.R n
def u (g : Grid) (n : ℕ) := ((g.N n : ℝ))⁻¹
def v (g : Grid) (d : ℕ) (n : ℕ) := ((g.R n)^d)⁻¹

theorem R_pos (g : Grid) (n : ℕ) : 0 < g.R n :=
  mul_pos (g.h_pos _) (Nat.cast_pos.mpr (g.m_pos n))
theorem u_pos (g : Grid) (n : ℕ) : 0 < g.u n := inv_pos.mpr (Nat.cast_pos.mpr (g.N_pos n))
theorem v_pos (g : Grid) (d n : ℕ) : 0 < g.v d n := inv_pos.mpr (pow_pos (g.R_pos n) _)
theorem u_zero (g : Grid) : Tendsto g.u atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp g.sample_grows)
theorem m_grows (g : Grid) : Tendsto g.m atTop atTop := by
  have hle (n : ℕ) : g.h n * (g.m n : ℝ) ≤ (g.m n : ℝ) :=
    mul_le_of_le_one_left (Nat.cast_nonneg _) (g.h_le_one _)
  have ht : Tendsto (fun n ↦ (g.m n : ℝ)) atTop atTop := tendsto_atTop_mono hle g.radius_grows
  exact tendsto_atTop.mpr fun b ↦ (ht.eventually_ge_atTop (b : ℝ)).mono
    fun _ h ↦ by exact_mod_cast h
theorem t_zero (g : Grid) (ν : ℝ) : Tendsto (g.t ν) atTop (𝓝 0) := by
  have hf := (tendsto_inv_atTop_zero.comp g.scaled_radius_grows).const_mul
    (Real.sqrt (2*ν)/(2*Real.pi))
  simpa only [mul_zero] using hf.congr (fun n ↦ by dsimp [t, frequencyScale, R]; ring)

end Grid
end MaternAudit.MaternParameters
