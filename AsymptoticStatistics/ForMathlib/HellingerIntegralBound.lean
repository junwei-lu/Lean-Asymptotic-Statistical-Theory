import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Constructions.Pi
import AsymptoticStatistics.ForMathlib.HellingerProduct

/-!
# Hellinger-bound on integral difference

For two probability measures `μ, ν` dominated by a common σ-finite measure `ξ`,
and a bounded measurable real-valued function `f`, the difference of integrals
`|∫ f dμ - ∫ f dν|` is controlled by the Hellinger `L²(ξ)`-residual:

```
|∫ f dμ - ∫ f dν| ≤ 2 · M · ‖√(dμ/dξ).toReal - √(dν/dξ).toReal‖_{L²(ξ)}
```

where `M = ‖f‖∞`. This is the analytic bridge between a Hellinger `eLpNorm`
output and an integral-of-test-function-difference statement consumed by a
weak-convergence transfer.

Proof sketch via the pointwise identity `p - q = (√p - √q)(√p + √q)` with
`p, q := (dμ/dξ).toReal, (dν/dξ).toReal`, followed by Cauchy-Schwarz on `L²(ξ)`
and the bound `‖√p + √q‖_{L²(ξ)} ≤ 2`.

Headline declarations: `integral_diff_le_two_mul_hellinger_eLpNorm` (base case),
its iid-product wrapper `integral_diff_le_hellinger_product_iid`, and the
weak-convergence transfer `integral_test_diff_tendsto_zero`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace AsymptoticStatistics.ForMathlib.HellingerIntegralBound

open AsymptoticStatistics.ForMathlib.RnDerivSqrt
open AsymptoticStatistics.ForMathlib.HellingerProduct

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Bounded-integral difference via Hellinger `L²`-residual* (base case).

For probability measures `μ, ν ≪ ξ` (with `ξ` σ-finite) and a bounded measurable
real-valued `f`, the difference of integrals is bounded by twice the supremum
norm times the Hellinger `L²(ξ)`-residual of the square-root densities.

See the file header for the proof sketch. -/
lemma integral_diff_le_two_mul_hellinger_eLpNorm
    (ξ : Measure Ω) [SigmaFinite ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ)
    (f : Ω → ℝ) (hf_meas : Measurable f) (M : ℝ) (hM_nn : 0 ≤ M)
    (hf_bound : ∀ ω, |f ω| ≤ M) :
    |∫ ω, f ω ∂μ - ∫ ω, f ω ∂ν|
      ≤ 2 * M *
        (eLpNorm (fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal
                            - Real.sqrt (ν.rnDeriv ξ ω).toReal) 2 ξ).toReal := by
  -- Set p := (μ.rnDeriv ξ).toReal, q := (ν.rnDeriv ξ).toReal, sp := √p, sq := √q.
  set sp : Ω → ℝ := fun ω => Real.sqrt (μ.rnDeriv ξ ω).toReal with hsp_def
  set sq : Ω → ℝ := fun ω => Real.sqrt (ν.rnDeriv ξ ω).toReal with hsq_def
  set A : Ω → ℝ := fun ω => sp ω - sq ω with hA_def
  set B : Ω → ℝ := fun ω => sp ω + sq ω with hB_def
  have hsp_nn : ∀ ω, 0 ≤ sp ω := fun ω => Real.sqrt_nonneg _
  have hsq_nn : ∀ ω, 0 ≤ sq ω := fun ω => Real.sqrt_nonneg _
  have hsp_meas : Measurable sp :=
    ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal).sqrt
  have hsq_meas : Measurable sq :=
    ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal).sqrt
  have hA_meas : Measurable A := hsp_meas.sub hsq_meas
  have hB_meas : Measurable B := hsp_meas.add hsq_meas
  have hB_nn : ∀ ω, 0 ≤ B ω := fun ω => add_nonneg (hsp_nn ω) (hsq_nn ω)
  -- L²-membership of sp, sq, A, B.
  have hsp_mem : MemLp sp 2 ξ := memLp_sqrt_rnDeriv hμ
  have hsq_mem : MemLp sq 2 ξ := memLp_sqrt_rnDeriv hν
  have hA_mem : MemLp A 2 ξ := hsp_mem.sub hsq_mem
  have hB_mem : MemLp B 2 ξ := hsp_mem.add hsq_mem
  -- Pointwise identity p - q = A · B (for p, q ≥ 0).
  have h_pt_factor : ∀ ω, (μ.rnDeriv ξ ω).toReal - (ν.rnDeriv ξ ω).toReal
      = A ω * B ω := by
    intro ω
    simp only [hA_def, hB_def, hsp_def, hsq_def]
    have h1 : Real.sqrt (μ.rnDeriv ξ ω).toReal ^ 2 = (μ.rnDeriv ξ ω).toReal :=
      Real.sq_sqrt ENNReal.toReal_nonneg
    have h2 : Real.sqrt (ν.rnDeriv ξ ω).toReal ^ 2 = (ν.rnDeriv ξ ω).toReal :=
      Real.sq_sqrt ENNReal.toReal_nonneg
    nlinarith [h1, h2, sq_nonneg (Real.sqrt (μ.rnDeriv ξ ω).toReal
      - Real.sqrt (ν.rnDeriv ξ ω).toReal),
      sq_nonneg (Real.sqrt (μ.rnDeriv ξ ω).toReal
        + Real.sqrt (ν.rnDeriv ξ ω).toReal)]
  -- Integral diff identity: ∫f dμ - ∫f dν = ∫ f · A · B dξ.
  have h_int_diff : ∫ ω, f ω ∂μ - ∫ ω, f ω ∂ν
      = ∫ ω, f ω * (A ω * B ω) ∂ξ := by
    rw [integral_eq_integral_mul_rnDeriv_of_ac hμ f,
        integral_eq_integral_mul_rnDeriv_of_ac hν f]
    rw [← integral_sub]
    · refine integral_congr_ae (Filter.Eventually.of_forall ?_)
      intro ω
      have hfac := h_pt_factor ω
      have h_target : f ω * (μ.rnDeriv ξ ω).toReal - f ω * (ν.rnDeriv ξ ω).toReal
          = f ω * (A ω * B ω) := by
        have : f ω * (μ.rnDeriv ξ ω).toReal - f ω * (ν.rnDeriv ξ ω).toReal
            = f ω * ((μ.rnDeriv ξ ω).toReal - (ν.rnDeriv ξ ω).toReal) := by ring
        rw [this, hfac]
      exact h_target
    · -- Integrability of f · (μ.rnDeriv ξ).toReal: bounded × integrable.
      have h_meas_mul_p : AEStronglyMeasurable
          (fun ω => f ω * (μ.rnDeriv ξ ω).toReal) ξ :=
        (hf_meas.mul ((Measure.measurable_rnDeriv μ ξ).ennreal_toReal)).aestronglyMeasurable
      refine ⟨h_meas_mul_p, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      have h_bd : ∀ ω, ‖f ω * (μ.rnDeriv ξ ω).toReal‖
          ≤ M * (μ.rnDeriv ξ ω).toReal := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_right (hf_bound ω) ENNReal.toReal_nonneg
      have h_finite :
          ∫⁻ ω, ENNReal.ofReal (M * (μ.rnDeriv ξ ω).toReal) ∂ξ < ∞ := by
        have h_eq : ∀ ω, ENNReal.ofReal (M * (μ.rnDeriv ξ ω).toReal)
            = ENNReal.ofReal M * ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal) := fun ω =>
          ENNReal.ofReal_mul hM_nn
        simp_rw [h_eq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have h_eq2 : ∀ᵐ ω ∂ξ, ENNReal.ofReal ((μ.rnDeriv ξ ω).toReal)
            = μ.rnDeriv ξ ω :=
          (Measure.rnDeriv_lt_top μ ξ).mono fun ω h =>
            ENNReal.ofReal_toReal (ne_of_lt h)
        rw [lintegral_congr_ae h_eq2, MeasureTheory.Measure.lintegral_rnDeriv hμ]
        simp [measure_univ]
      refine lt_of_le_of_lt ?_ h_finite
      refine lintegral_mono_ae (Filter.Eventually.of_forall ?_)
      intro ω
      exact ENNReal.ofReal_le_ofReal (h_bd ω)
    · have h_meas_mul_q : AEStronglyMeasurable
          (fun ω => f ω * (ν.rnDeriv ξ ω).toReal) ξ :=
        (hf_meas.mul ((Measure.measurable_rnDeriv ν ξ).ennreal_toReal)).aestronglyMeasurable
      refine ⟨h_meas_mul_q, ?_⟩
      rw [hasFiniteIntegral_iff_norm]
      have h_bd : ∀ ω, ‖f ω * (ν.rnDeriv ξ ω).toReal‖
          ≤ M * (ν.rnDeriv ξ ω).toReal := by
        intro ω
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
        exact mul_le_mul_of_nonneg_right (hf_bound ω) ENNReal.toReal_nonneg
      have h_finite :
          ∫⁻ ω, ENNReal.ofReal (M * (ν.rnDeriv ξ ω).toReal) ∂ξ < ∞ := by
        have h_eq : ∀ ω, ENNReal.ofReal (M * (ν.rnDeriv ξ ω).toReal)
            = ENNReal.ofReal M * ENNReal.ofReal ((ν.rnDeriv ξ ω).toReal) := fun ω =>
          ENNReal.ofReal_mul hM_nn
        simp_rw [h_eq]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have h_eq2 : ∀ᵐ ω ∂ξ, ENNReal.ofReal ((ν.rnDeriv ξ ω).toReal)
            = ν.rnDeriv ξ ω :=
          (Measure.rnDeriv_lt_top ν ξ).mono fun ω h =>
            ENNReal.ofReal_toReal (ne_of_lt h)
        rw [lintegral_congr_ae h_eq2, MeasureTheory.Measure.lintegral_rnDeriv hν]
        simp [measure_univ]
      refine lt_of_le_of_lt ?_ h_finite
      refine lintegral_mono_ae (Filter.Eventually.of_forall ?_)
      intro ω
      exact ENNReal.ofReal_le_ofReal (h_bd ω)
  -- Reassociate f · (A · B) = A · (f · B).
  have h_assoc : ∀ ω, f ω * (A ω * B ω) = A ω * (f ω * B ω) := fun ω => by ring
  rw [h_int_diff]
  rw [integral_congr_ae (Filter.Eventually.of_forall h_assoc)]
  -- Now apply Cauchy–Schwarz: |∫ A · (f·B) dξ| ≤ √(∫ A² dξ) · √(∫ (f·B)² dξ).
  -- First need: f · B ∈ L²(ξ).
  have hfB_meas : Measurable (fun ω => f ω * B ω) := hf_meas.mul hB_meas
  have hfB_bd : ∀ ω, |f ω * B ω| ≤ M * B ω := by
    intro ω
    rw [abs_mul, abs_of_nonneg (hB_nn ω)]
    exact mul_le_mul_of_nonneg_right (hf_bound ω) (hB_nn ω)
  -- ‖f·B‖² ≤ M² · B² pointwise.
  have hfB_sq_bd : ∀ ω, (f ω * B ω) ^ 2 ≤ M ^ 2 * B ω ^ 2 := by
    intro ω
    have h1 : (f ω * B ω) ^ 2 = (f ω) ^ 2 * B ω ^ 2 := by ring
    have h2 : (f ω) ^ 2 ≤ M ^ 2 := by
      have := hf_bound ω
      have h_f_abs : |f ω| ≤ M := this
      nlinarith [sq_nonneg (f ω), abs_nonneg (f ω), sq_abs (f ω)]
    rw [h1]
    exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
  have hB_sq_int : Integrable (fun ω => B ω ^ 2) ξ := hB_mem.integrable_sq
  have hfB_sq_int : Integrable (fun ω => (f ω * B ω) ^ 2) ξ := by
    refine Integrable.mono (hB_sq_int.const_mul (M ^ 2))
      (hfB_meas.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hr_nn : 0 ≤ M ^ 2 * B ω ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    rw [show ‖M ^ 2 * B ω ^ 2‖ = M ^ 2 * B ω ^ 2 from by
      rw [Real.norm_eq_abs, abs_of_nonneg hr_nn]]
    exact hfB_sq_bd ω
  have hfB_mem : MemLp (fun ω => f ω * B ω) 2 ξ := by
    rw [memLp_two_iff_integrable_sq hfB_meas.aestronglyMeasurable]
    exact hfB_sq_int
  -- Cauchy-Schwarz on real-valued L²:
  have h_cs := AsymptoticStatistics.L2Utils.abs_integral_mul_le_sqrt_integral_sq
    ξ hA_mem hfB_mem
  -- |∫ A · (f·B) dξ| ≤ √(∫A² dξ) · √(∫(f·B)² dξ).
  -- Now bound √(∫(f·B)² dξ) ≤ M · √(∫B² dξ).
  have hA_sq_nn : 0 ≤ ∫ ω, A ω ^ 2 ∂ξ :=
    integral_nonneg fun _ => sq_nonneg _
  have hfB_sq_nn : 0 ≤ ∫ ω, (f ω * B ω) ^ 2 ∂ξ :=
    integral_nonneg fun _ => sq_nonneg _
  have hB_sq_nn : 0 ≤ ∫ ω, B ω ^ 2 ∂ξ :=
    integral_nonneg fun _ => sq_nonneg _
  have h_fB_sq_le_MsqBsq : ∫ ω, (f ω * B ω) ^ 2 ∂ξ ≤ M ^ 2 * ∫ ω, B ω ^ 2 ∂ξ := by
    rw [← integral_const_mul]
    exact integral_mono hfB_sq_int (hB_sq_int.const_mul (M^2))
      (fun ω => hfB_sq_bd ω)
  have h_sqrt_fB_le : Real.sqrt (∫ ω, (f ω * B ω) ^ 2 ∂ξ)
      ≤ M * Real.sqrt (∫ ω, B ω ^ 2 ∂ξ) := by
    have h_sqrt_mono := Real.sqrt_le_sqrt h_fB_sq_le_MsqBsq
    have h_eq : Real.sqrt (M ^ 2 * ∫ ω, B ω ^ 2 ∂ξ)
        = M * Real.sqrt (∫ ω, B ω ^ 2 ∂ξ) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hM_nn]
    linarith [h_sqrt_mono, h_eq.le, h_eq.ge]
  -- Now bound ∫B² dξ ≤ 4 (since B = √p + √q, ∫B² = 2 + 2A ≤ 4).
  -- ∫B² = ∫(sp + sq)² = ∫sp² + 2∫sp·sq + ∫sq² = 1 + 2A + 1 = 2 + 2A.
  have hsp_sq_int : Integrable (fun ω => sp ω ^ 2) ξ := hsp_mem.integrable_sq
  have hsq_sq_int : Integrable (fun ω => sq ω ^ 2) ξ := hsq_mem.integrable_sq
  have hspsq_int : Integrable (fun ω => sp ω * sq ω) ξ :=
    hsp_mem.integrable_mul hsq_mem
  have hsp_sq_val : ∫ ω, sp ω ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := μ) (μ := ξ) hμ
    simpa [hsp_def, measure_univ] using this
  have hsq_sq_val : ∫ ω, sq ω ^ 2 ∂ξ = 1 := by
    have := integral_sqrt_rnDeriv_sq (ν := ν) (μ := ξ) hν
    simpa [hsq_def, measure_univ] using this
  have hA_aff_nn : 0 ≤ ∫ ω, sp ω * sq ω ∂ξ :=
    integral_sqrt_mul_sqrt_nonneg μ ν ξ
  have hA_aff_le_one : ∫ ω, sp ω * sq ω ∂ξ ≤ 1 :=
    integral_sqrt_mul_sqrt_le_one hμ hν
  -- ∫B² = 2 + 2 · affinity ≤ 4.
  have hB_sq_eq : ∫ ω, B ω ^ 2 ∂ξ
      = 2 + 2 * ∫ ω, sp ω * sq ω ∂ξ := by
    have h_pt : ∀ ω, B ω ^ 2 = sp ω ^ 2 + 2 * (sp ω * sq ω) + sq ω ^ 2 := by
      intro ω; simp only [hB_def]; ring
    have h_int_eq :
        ∫ ω, B ω ^ 2 ∂ξ
          = (∫ ω, sp ω ^ 2 ∂ξ) + 2 * (∫ ω, sp ω * sq ω ∂ξ)
              + (∫ ω, sq ω ^ 2 ∂ξ) := by
      calc ∫ ω, B ω ^ 2 ∂ξ
          = ∫ ω, sp ω ^ 2 + 2 * (sp ω * sq ω) + sq ω ^ 2 ∂ξ :=
            integral_congr_ae (Filter.Eventually.of_forall h_pt)
        _ = (∫ ω, sp ω ^ 2 + 2 * (sp ω * sq ω) ∂ξ) + ∫ ω, sq ω ^ 2 ∂ξ :=
            integral_add (hsp_sq_int.add (hspsq_int.const_mul 2)) hsq_sq_int
        _ = (∫ ω, sp ω ^ 2 ∂ξ) + (∫ ω, 2 * (sp ω * sq ω) ∂ξ)
              + ∫ ω, sq ω ^ 2 ∂ξ := by
            rw [integral_add hsp_sq_int (hspsq_int.const_mul 2)]
        _ = (∫ ω, sp ω ^ 2 ∂ξ) + 2 * (∫ ω, sp ω * sq ω ∂ξ)
              + ∫ ω, sq ω ^ 2 ∂ξ := by
            rw [integral_const_mul]
    rw [h_int_eq, hsp_sq_val, hsq_sq_val]
    ring
  have hB_sq_le : ∫ ω, B ω ^ 2 ∂ξ ≤ 4 := by
    rw [hB_sq_eq]; linarith
  have h_sqrt_B_le : Real.sqrt (∫ ω, B ω ^ 2 ∂ξ) ≤ 2 := by
    have h1 := Real.sqrt_le_sqrt hB_sq_le
    have h2 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  -- Combine: |∫ A · (f·B)| ≤ √(∫A²) · √(∫(f·B)²) ≤ √(∫A²) · M · 2 = 2M · √(∫A²).
  have h_sqrt_A_nn : 0 ≤ Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) := Real.sqrt_nonneg _
  have h_chain :
      Real.sqrt (∫ ω, A ω ^ 2 ∂ξ)
        * Real.sqrt (∫ ω, (f ω * B ω) ^ 2 ∂ξ)
      ≤ Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) * (M * 2) := by
    have h_step1 :
        Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) * Real.sqrt (∫ ω, (f ω * B ω) ^ 2 ∂ξ)
          ≤ Real.sqrt (∫ ω, A ω ^ 2 ∂ξ)
              * (M * Real.sqrt (∫ ω, B ω ^ 2 ∂ξ)) :=
      mul_le_mul_of_nonneg_left h_sqrt_fB_le h_sqrt_A_nn
    have h_step2 :
        Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) * (M * Real.sqrt (∫ ω, B ω ^ 2 ∂ξ))
          ≤ Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) * (M * 2) := by
      have h_M_nn : 0 ≤ M := hM_nn
      have : M * Real.sqrt (∫ ω, B ω ^ 2 ∂ξ) ≤ M * 2 :=
        mul_le_mul_of_nonneg_left h_sqrt_B_le h_M_nn
      exact mul_le_mul_of_nonneg_left this h_sqrt_A_nn
    linarith
  have h_final_real :
      |∫ ω, A ω * (f ω * B ω) ∂ξ|
        ≤ Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) * (M * 2) := le_trans h_cs h_chain
  -- Now convert √(∫ A² dξ) to (eLpNorm A 2 ξ).toReal.
  -- (eLpNorm A 2 ξ).toReal = (∫ ‖A‖^2 dξ)^(1/2) = √(∫ A² dξ).
  have h_eLp_eq :
      (eLpNorm A 2 ξ).toReal = Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) := by
    rw [hA_mem.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h_two]
    have h_pt : ∀ ω, ‖A ω‖ ^ (2 : ℝ) = A ω ^ 2 := by
      intro ω
      rw [show ((2 : ℝ) = ((2 : ℕ) : ℝ)) from by norm_num,
          Real.rpow_natCast, Real.norm_eq_abs, sq_abs]
    have h_int_eq : ∫ ω, ‖A ω‖ ^ (2 : ℝ) ∂ξ = ∫ ω, A ω ^ 2 ∂ξ := by
      refine integral_congr_ae (Filter.Eventually.of_forall h_pt)
    rw [h_int_eq]
    have h_rpow : (∫ ω, A ω ^ 2 ∂ξ) ^ (2 : ℝ)⁻¹ = Real.sqrt (∫ ω, A ω ^ 2 ∂ξ) := by
      rw [show ((2 : ℝ)⁻¹) = (1 / 2 : ℝ) from by norm_num]
      rw [← Real.sqrt_eq_rpow]
    rw [h_rpow]
    rw [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)]
  rw [h_eLp_eq]
  -- Final assembly: 2 * M * √(∫A²) = √(∫A²) * (M * 2).
  linarith [h_final_real]

/-- *Bounded-integral difference via product-Hellinger `L²`-residual* (iid wrap).

For two probability measures `μ, ν` per coordinate (both `≪` the same σ-finite
dominator `ξ`), the integral-difference on the iid product measures `μ^n, ν^n`
against a bounded measurable test function `F` is bounded by `2 · M ·` the
product-Hellinger eLpNorm of the per-coordinate sqrt-densities:

```
|∫ F d(μ^n) - ∫ F d(ν^n)|
  ≤ 2 · M ·
    ‖√(∏ⱼ (dμ/dξ)(X j)).toReal - √(∏ⱼ (dν/dξ)(X j)).toReal‖_{L²(ξ^n)}.
```

The RHS is exactly the shape produced by
`hellinger_locality_for_qmdpath_same_score`. -/
lemma integral_diff_le_hellinger_product_iid
    (ξ : Measure Ω) [SigmaFinite ξ]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : μ ≪ ξ) (hν : ν ≪ ξ) (n : ℕ)
    (F : (Fin n → Ω) → ℝ) (hF_meas : Measurable F)
    (M : ℝ) (hM_nn : 0 ≤ M) (hF_bound : ∀ X, |F X| ≤ M) :
    |∫ X, F X ∂(MeasureTheory.Measure.pi (fun _ : Fin n => μ))
       - ∫ X, F X ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ν))|
      ≤ 2 * M *
        (eLpNorm
          (fun X : Fin n → Ω =>
            Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
            - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal)
          2 (MeasureTheory.Measure.pi (fun _ : Fin n => ξ))).toReal := by
  -- Abbreviations for the product measures.
  set μn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ) with hμn_def
  set νn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ν) with hνn_def
  set ξn : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => ξ) with hξn_def
  -- Instances.
  haveI : IsProbabilityMeasure μn := by rw [hμn_def]; infer_instance
  haveI : IsProbabilityMeasure νn := by rw [hνn_def]; infer_instance
  haveI : SigmaFinite ξn := by rw [hξn_def]; infer_instance
  -- Densities and product-density identity for μ^n ≪ ξ^n.
  -- μ = ξ.withDensity (μ.rnDeriv ξ) and similarly for ν.
  have hμ_eq : μ = ξ.withDensity (μ.rnDeriv ξ) :=
    (Measure.withDensity_rnDeriv_eq μ ξ hμ).symm
  have hν_eq : ν = ξ.withDensity (ν.rnDeriv ξ) :=
    (Measure.withDensity_rnDeriv_eq ν ξ hν).symm
  -- ξ.withDensity (μ.rnDeriv ξ) is σ-finite (= μ), hence the iid version is σ-finite.
  haveI : SigmaFinite (ξ.withDensity (μ.rnDeriv ξ)) := by
    rw [← hμ_eq]; infer_instance
  haveI : SigmaFinite (ξ.withDensity (ν.rnDeriv ξ)) := by
    rw [← hν_eq]; infer_instance
  -- Product density identity for μn.
  have h_μ_rnDeriv_meas : Measurable (μ.rnDeriv ξ) := Measure.measurable_rnDeriv μ ξ
  have h_ν_rnDeriv_meas : Measurable (ν.rnDeriv ξ) := Measure.measurable_rnDeriv ν ξ
  have hμn_withDensity :
      μn = ξn.withDensity (fun X : Fin n → Ω => ∏ j, μ.rnDeriv ξ (X j)) := by
    rw [hμn_def, hξn_def]
    rw [show (fun _ : Fin n => μ) = (fun _ : Fin n => ξ.withDensity (μ.rnDeriv ξ))
        from funext fun _ => hμ_eq]
    rw [← MeasureTheory.pi_withDensity_prod (fun _ : Fin n => h_μ_rnDeriv_meas)]
  have hνn_withDensity :
      νn = ξn.withDensity (fun X : Fin n → Ω => ∏ j, ν.rnDeriv ξ (X j)) := by
    rw [hνn_def, hξn_def]
    rw [show (fun _ : Fin n => ν) = (fun _ : Fin n => ξ.withDensity (ν.rnDeriv ξ))
        from funext fun _ => hν_eq]
    rw [← MeasureTheory.pi_withDensity_prod (fun _ : Fin n => h_ν_rnDeriv_meas)]
  -- μn ≪ ξn, νn ≪ ξn.
  have hμn_ac : μn ≪ ξn := by
    rw [hμn_withDensity]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  have hνn_ac : νn ≪ ξn := by
    rw [hνn_withDensity]; exact MeasureTheory.withDensity_absolutelyContinuous _ _
  -- rnDeriv identity: (μn).rnDeriv ξn =ᵐ[ξn] (fun X => ∏ⱼ μ.rnDeriv ξ (X j)).
  have h_prod_meas_μ : Measurable
      (fun X : Fin n → Ω => ∏ j, μ.rnDeriv ξ (X j)) :=
    Finset.measurable_prod _ (fun j _ => h_μ_rnDeriv_meas.comp (measurable_pi_apply j))
  have h_prod_meas_ν : Measurable
      (fun X : Fin n → Ω => ∏ j, ν.rnDeriv ξ (X j)) :=
    Finset.measurable_prod _ (fun j _ => h_ν_rnDeriv_meas.comp (measurable_pi_apply j))
  have hμn_rnDeriv_eq : μn.rnDeriv ξn
      =ᵐ[ξn] fun X : Fin n → Ω => ∏ j, μ.rnDeriv ξ (X j) := by
    rw [hμn_withDensity]
    exact Measure.rnDeriv_withDensity _ h_prod_meas_μ
  have hνn_rnDeriv_eq : νn.rnDeriv ξn
      =ᵐ[ξn] fun X : Fin n → Ω => ∏ j, ν.rnDeriv ξ (X j) := by
    rw [hνn_withDensity]
    exact Measure.rnDeriv_withDensity _ h_prod_meas_ν
  -- Apply the base lemma to μn vs νn over ξn.
  have h_base :=
    integral_diff_le_two_mul_hellinger_eLpNorm ξn μn νn hμn_ac hνn_ac
      F hF_meas M hM_nn hF_bound
  -- The integrand of the eLpNorm in `h_base` is
  --   √((μn.rnDeriv ξn) X).toReal - √((νn.rnDeriv ξn) X).toReal
  -- which we rewrite ξn-a.e. to
  --   √(∏ⱼ μ.rnDeriv ξ (X j)).toReal - √(∏ⱼ ν.rnDeriv ξ (X j)).toReal
  -- via `hμn_rnDeriv_eq` and `hνn_rnDeriv_eq`. We use `eLpNorm_congr_ae`.
  have h_ae_eq :
      (fun X : Fin n → Ω =>
          Real.sqrt (μn.rnDeriv ξn X).toReal
            - Real.sqrt (νn.rnDeriv ξn X).toReal)
        =ᵐ[ξn] fun X : Fin n → Ω =>
          Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
            - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal := by
    filter_upwards [hμn_rnDeriv_eq, hνn_rnDeriv_eq] with X hμX hνX
    rw [hμX, hνX]
  have h_eLp_eq : eLpNorm (fun X : Fin n → Ω =>
        Real.sqrt (μn.rnDeriv ξn X).toReal
          - Real.sqrt (νn.rnDeriv ξn X).toReal) 2 ξn
      = eLpNorm (fun X : Fin n → Ω =>
        Real.sqrt (∏ j, μ.rnDeriv ξ (X j)).toReal
          - Real.sqrt (∏ j, ν.rnDeriv ξ (X j)).toReal) 2 ξn :=
    MeasureTheory.eLpNorm_congr_ae h_ae_eq
  rw [h_eLp_eq] at h_base
  exact h_base

/-- *Weak-convergence transfer between two iid product sequences.*

For two sequences of probability measures `μ_n, ν_n : Measure Ω` (both `≪` the
same σ-finite dominator `ξ`, and indexed measurably), if the Hellinger
`L²(ξ^n)`-residual of `√(∏ⱼ (dμ_n/dξ)(X j)) - √(∏ⱼ (dν_n/dξ)(X j))` tends to
`0` as `n → ∞`, then for any **fixed** bounded continuous test functional
applied to a (varying) measurable transform `F_n : (Fin n → Ω) → ℝ`,

```
∫ f (F_n X) ∂(μ_n^n) - ∫ f (F_n X) ∂(ν_n^n) → 0.
```

This absorbs the Hellinger `eLpNorm → 0` input into a
"test-functional-integral-difference → 0" output, consumable by a
triangle-inequality assembly.

### Proof

Apply `integral_diff_le_hellinger_product_iid` per `n` (with `F` instantiated
at `f ∘ F_n n`), then squeeze using the Hellinger eLpNorm → 0 hypothesis. -/
lemma integral_test_diff_tendsto_zero
    (ξ : Measure Ω) [SigmaFinite ξ]
    (μ ν : ℕ → Measure Ω)
    [hμ_prob : ∀ n, IsProbabilityMeasure (μ n)]
    [hν_prob : ∀ n, IsProbabilityMeasure (ν n)]
    (_hμ_dom : ∀ n, μ n ≪ ξ) (_hν_dom : ∀ n, ν n ≪ ξ)
    (F : ∀ n, (Fin n → Ω) → ℝ) (_hF_meas : ∀ n, Measurable (F n))
    (f : BoundedContinuousFunction ℝ ℝ)
    (h_hellinger :
        Tendsto
          (fun n : ℕ =>
            (eLpNorm
              (fun X : Fin n → Ω =>
                Real.sqrt (∏ j, (μ n).rnDeriv ξ (X j)).toReal
                - Real.sqrt (∏ j, (ν n).rnDeriv ξ (X j)).toReal)
              2 (MeasureTheory.Measure.pi (fun _ : Fin n => ξ))).toReal)
          atTop (𝓝 (0 : ℝ))) :
    Tendsto
      (fun n : ℕ =>
        |∫ X, f (F n X) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => μ n))
           - ∫ X, f (F n X) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ν n))|)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  set M : ℝ := ‖f‖ with hM_def
  have hM_nn : 0 ≤ M := norm_nonneg _
  have hf_bound : ∀ y : ℝ, |f y| ≤ M := fun y => by
    simpa [hM_def, Real.norm_eq_abs] using (f.norm_coe_le_norm y)
  have hf_comp_bound : ∀ n (X : Fin n → Ω), |f (F n X)| ≤ M := fun n X =>
    hf_bound _
  have h_bound : ∀ n,
      |∫ X, f (F n X) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => μ n))
         - ∫ X, f (F n X) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => ν n))|
        ≤ 2 * M *
          (eLpNorm
            (fun X : Fin n → Ω =>
              Real.sqrt (∏ j, (μ n).rnDeriv ξ (X j)).toReal
              - Real.sqrt (∏ j, (ν n).rnDeriv ξ (X j)).toReal)
            2 (MeasureTheory.Measure.pi (fun _ : Fin n => ξ))).toReal := fun n =>
    integral_diff_le_hellinger_product_iid ξ (μ n) (ν n) (_hμ_dom n) (_hν_dom n) n
      (fun X => f (F n X)) (f.continuous.measurable.comp (_hF_meas n)) M hM_nn
      (hf_comp_bound n)
  have h_lim : Tendsto (fun n => 2 * M *
      (eLpNorm
        (fun X : Fin n → Ω =>
          Real.sqrt (∏ j, (μ n).rnDeriv ξ (X j)).toReal
          - Real.sqrt (∏ j, (ν n).rnDeriv ξ (X j)).toReal)
        2 (MeasureTheory.Measure.pi (fun _ : Fin n => ξ))).toReal)
      atTop (𝓝 0) := by
    have := h_hellinger.const_mul (2 * M)
    simpa using this
  exact squeeze_zero (fun n => abs_nonneg _) h_bound h_lim

end AsymptoticStatistics.ForMathlib.HellingerIntegralBound
