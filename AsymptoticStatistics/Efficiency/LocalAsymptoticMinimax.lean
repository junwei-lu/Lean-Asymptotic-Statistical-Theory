import AsymptoticStatistics.LocalAsymptoticNormality.LANExpansion
import AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation
import AsymptoticStatistics.ForMathlib.Anderson
import AsymptoticStatistics.ForMathlib.BowlShaped
import AsymptoticStatistics.ForMathlib.DiagonalSubseqLimSupFinset
import AsymptoticStatistics.ForMathlib.GaussianMGF
import AsymptoticStatistics.Experiment.LeCamRepresentation
import AsymptoticStatistics.ForMathlib.MultivariateGaussianWeakLimit
import AsymptoticStatistics.ForMathlib.PortmanteauLscBridge
import AsymptoticStatistics.ForMathlib.Prohorov
import AsymptoticStatistics.ForMathlib.SlutskyFrechetShift
import AsymptoticStatistics.Experiment.GaussianShiftMinimax
import Mathlib.Probability.Decision.Risk.Defs
import Mathlib.Probability.Decision.Risk.Basic

/-!
# Theorem 8.11 — Local Asymptotic Minimax Bound

Reference: van der Vaart, *Asymptotic Statistics* §8.7.

For a parametric family DQM at `θ₀` with non-singular Fisher information `J`,
a Fréchet-differentiable functional `ψ` with derivative `ψ̇`, and a bowl-shaped
loss `L`, every estimator sequence `T_n` satisfies the local asymptotic minimax
bound

    sup_{I ⊂ ℝᵏ, finite}  liminf_n  sup_{h ∈ I}
        ∫ L(√n (T_n - ψ(θ₀ + h/√n))) dP^n_{θ₀ + h/√n}
      ≥  ∫ L dN(0, ψ̇ · J⁻¹ · ψ̇ᵀ).

The Gaussian integral on the right is the asymptotic minimax risk: no estimator
sequence can do strictly better, locally, against the worst-case finite family
of alternatives.

Headline declaration: `local_asymptotic_minimax_bound`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace ENNReal MatrixOrder

namespace AsymptoticStatistics
namespace LocalAsymptoticMinimax

variable {k d : ℕ}
variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- Parameter space (same convention as Theorem 7.10). -/
abbrev Θ (k : ℕ) : Type := EuclideanSpace ℝ (Fin k)

/-- Target space of the statistic and the functional `ψ`. -/
abbrev 𝓨 (d : ℕ) : Type := EuclideanSpace ℝ (Fin d)

/-- The local asymptotic L-risk of an estimator sequence `T` at `θ₀` — the LHS of 8.11.

    `⨆_{I ⊂ Θ, finite} liminf_n ⨆_{h ∈ I} ∫ L(√n (T_n - ψ(θ₀ + h/√n))) dP^n_{θ₀+h/√n}`.

This is the worst-case asymptotic L-risk over local finite alternatives —
the natural "minimax-style" performance measure. The conclusion of 8.11
states this is bounded below by the Gaussian-shift integral on the limit
covariance `Σ_ψ := ψDot · J⁻¹ · ψDotᵀ`. -/
noncomputable def localAsymptoticRisk
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) (θ₀ : Θ k)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (ψ : Θ k → 𝓨 d)
    (L : 𝓨 d → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ I : Finset (Θ k), Filter.liminf
    (fun n : ℕ => ⨆ h ∈ I,
      ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
    Filter.atTop

/-- ## **Step E — Bowl-shaped truncation extends bounded conclusion to unbounded `L`**.

If the local-asymptotic minimax bound holds for every truncation
`L_N := fun y => min (L y) N` (which is bounded), then it holds for `L` itself.

**Proof outline**:

1. **LHS monotone in N**: `L_N ↗ L` pointwise as `N → ∞`, so the integrand of
   `localAsymptoticRisk` is monotone in N, hence `localAsymptoticRisk_N ≤
   localAsymptoticRisk` (with `_N` indicating the truncated loss).
   Therefore: `sup_N localAsymptoticRisk_N ≤ localAsymptoticRisk`.
   But also each truncated risk is ≥ truncated RHS, so
   `sup_N localAsymptoticRisk_N ≥ sup_N (truncated RHS)`.

2. **RHS monotone via MCT**: `L_N ↗ L` pointwise + nonneg ⇒
   `∫ L_N dN(0, Σ) ↗ ∫ L dN(0, Σ)` by `MeasureTheory.lintegral_iSup`.

3. **Combine**:
   `localAsymptoticRisk ≥ sup_N localAsymptoticRisk_N ≥ sup_N (∫ L_N dN(0, Σ)) =
    ∫ L dN(0, Σ)`. -/
theorem lam_truncation_of_bowl_shaped
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) (θ₀ : Θ k)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (ψ : Θ k → 𝓨 d)
    (L : 𝓨 d → ℝ≥0∞) (hL_bowl : BowlShaped L)
    (S_target : Matrix (Fin d) (Fin d) ℝ) (_hS : S_target.PosSemidef)
    (h_truncated : ∀ N : ℕ,
      localAsymptoticRisk M μ θ₀ T ψ (fun y => min (L y) N)
        ≥ ∫⁻ y, min (L y) (N : ℝ≥0∞)
              ∂(multivariateGaussian (0 : 𝓨 d) S_target)) :
    localAsymptoticRisk M μ θ₀ T ψ L
      ≥ ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d) S_target) := by
  -- Step 1: pointwise `L y = ⨆ N, min (L y) N` (truncation family converges to L).
  have h_pt : ∀ y : 𝓨 d, L y = ⨆ N : ℕ, min (L y) (N : ℝ≥0∞) := by
    intro y
    refine le_antisymm ?_ (iSup_le fun N => min_le_left _ _)
    by_cases h_top : L y = ⊤
    · -- `L y = ⊤`: `⨆ N min ⊤ N = ⨆ N N = ⊤`.
      rw [h_top]
      have heq : (fun N : ℕ => min (⊤ : ℝ≥0∞) (N : ℝ≥0∞))
          = (fun N : ℕ => (N : ℝ≥0∞)) :=
        funext fun _ => min_eq_right le_top
      rw [heq, ENNReal.iSup_natCast]
    · -- `L y < ⊤`: pick `N` with `L y ≤ N`, then `min (L y) N = L y`.
      obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt h_top
      refine le_iSup_of_le N ?_
      exact (min_eq_left hN.le).ge
  -- Step 2: MCT — `∫⁻ L = ⨆ N ∫⁻ min(L, N)`.
  have h_int : ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d) S_target)
      = ⨆ N : ℕ,
          ∫⁻ y, min (L y) (N : ℝ≥0∞) ∂(multivariateGaussian (0 : 𝓨 d) S_target) := by
    conv_lhs => rw [show (fun y => L y) = (fun y => ⨆ N : ℕ, min (L y) (N : ℝ≥0∞)) from
      funext h_pt]
    refine MeasureTheory.lintegral_iSup (fun N => hL_bowl.measurable.min measurable_const) ?_
    intro N₁ N₂ hN y
    exact min_le_min le_rfl (by exact_mod_cast hN)
  -- Step 3: monotonicity of `localAsymptoticRisk` in `L`.
  have h_mono : ∀ N : ℕ, localAsymptoticRisk M μ θ₀ T ψ (fun y => min (L y) N)
      ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
    intro N
    refine iSup_le fun I => le_iSup_of_le I ?_
    refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
    refine iSup_le fun h => le_iSup_of_le h ?_
    refine iSup_le fun hI => le_iSup_of_le hI ?_
    exact MeasureTheory.lintegral_mono fun _ => min_le_left _ _
  -- Combine: ∫⁻ L = ⨆_N RHS_N ≤ ⨆_N LHS_N ≤ LHS.
  rw [h_int]
  exact iSup_le fun N => le_trans (h_truncated N) (h_mono N)

/-- ## **Step A — `localAsymptoticRisk` lower-bounded by sub-prob averaged risk**.

For any finite set `I ⊂ Θ` and any sub-probability assignment `π : Θ → ℝ≥0`
with `∑ h ∈ I, π h ≤ 1`, the discrete-prior averaged risk along the LAN
sequence is bounded above by `localAsymptoticRisk`:

    `liminf_n  ∑_{h ∈ I} π h · ∫⁻ L(√n (T_n - ψ(θ₀+h/√n))) dP^n_{θ₀+h/√n}`
    `≤ localAsymptoticRisk M μ θ₀ T ψ L`.

**Proof**: pure pointwise sup-vs-avg. For each `n`, `∑_{h ∈ I} π h · x_{n,h}
≤ (∑_{h ∈ I} π h) · ⨆_{h ∈ I} x_{n,h} ≤ 1 · ⨆_{h ∈ I} x_{n,h}`. Then
`liminf` is monotone, and `liminf_n ⨆_{h ∈ I} x_{n,h} ≤ ⨆_{I'} liminf_n
⨆_{h ∈ I'} x_{n,h} = localAsymptoticRisk` via `le_iSup` at `I' := I`.

This is **Step A** of the Bayesian + truncation proof — the first link in the
chain `localAsymptoticRisk ≥ liminf bayesRisk_n ≥ bayesRisk_∞ = bayesRiskAtTau`. -/
lemma localAsymptoticRisk_ge_avg_lower_bound
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k) (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (ψ : Θ k → 𝓨 d) (L : 𝓨 d → ℝ≥0∞)
    (I : Finset (Θ k)) (π : Θ k → NNReal)
    (hπ_sum : (∑ h ∈ I, (π h : ℝ≥0∞)) ≤ 1) :
    Filter.liminf (fun n : ℕ => ∑ h ∈ I, (π h : ℝ≥0∞) *
      ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n))
    Filter.atTop
    ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
  set x : ℕ → Θ k → ℝ≥0∞ := fun n h =>
    ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
          ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) with hx_def
  have h_per_n : ∀ n, (∑ h ∈ I, (π h : ℝ≥0∞) * x n h) ≤ ⨆ h ∈ I, x n h := by
    intro n
    calc (∑ h ∈ I, (π h : ℝ≥0∞) * x n h)
        ≤ ∑ h ∈ I, (π h : ℝ≥0∞) * (⨆ h' ∈ I, x n h') := by
          apply Finset.sum_le_sum
          intro h hI
          exact mul_le_mul_right (le_iSup₂_of_le h hI le_rfl) (π h : ℝ≥0∞)
      _ = (∑ h ∈ I, (π h : ℝ≥0∞)) * (⨆ h' ∈ I, x n h') := by
          rw [← Finset.sum_mul]
      _ ≤ 1 * (⨆ h' ∈ I, x n h') :=
          mul_le_mul_left hπ_sum (⨆ h' ∈ I, x n h')
      _ = ⨆ h' ∈ I, x n h' := one_mul _
  have h_liminf :
      Filter.liminf (fun n => ∑ h ∈ I, (π h : ℝ≥0∞) * x n h) atTop
        ≤ Filter.liminf (fun n => ⨆ h ∈ I, x n h) atTop :=
    Filter.liminf_le_liminf (Filter.Eventually.of_forall h_per_n)
  have h_iSup :
      Filter.liminf (fun n => ⨆ h ∈ I, x n h) atTop ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
    change Filter.liminf (fun n => ⨆ h ∈ I, x n h) atTop ≤
      ⨆ I' : Finset (Θ k), Filter.liminf (fun n : ℕ => ⨆ h ∈ I', x n h) atTop
    exact le_iSup
      (fun I' : Finset (Θ k) => Filter.liminf (fun n : ℕ => ⨆ h ∈ I', x n h) atTop) I
  exact h_liminf.trans h_iSup

/-! ## LAN Bayes-risk plumbing — bridge from Step A to Mathlib `bayesRisk` framework

These definitions wrap the LAN experiment data into Mathlib's `bayesRisk` /
`avgRisk` API. They turn the discrete-prior averaged-risk inequality of Step A
into a `bayesRisk`-form lower bound, which is the natural input for the
substantive Step B (LAN-Bayes limit). The kernel construction itself
(`P_n h := productMeasure M μ (θ₀ + (√n)⁻¹ • h) n` measurable in `h`) is
parametrized in by the caller — joint measurability of `(h, x) ↦ density (...) x`
is not provided by `ParametricFamily`, so kernel construction is deferred. -/

/-- LAN-experiment loss: rescaled discrepancy `√n • (y - ψ(θ₀ + h/√n))`. -/
noncomputable def lanLoss (θ₀ : Θ k) (ψ : Θ k → 𝓨 d) (L : 𝓨 d → ℝ≥0∞) (n : ℕ) :
    Θ k → 𝓨 d → ℝ≥0∞ :=
  fun h y => L ((Real.sqrt n) • (y - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))

/-- Per-`h` measurability of the LAN loss as a function of `y`. Used for
`lintegral_map`-style rewrites in the avgRisk identification. -/
lemma lanLoss_measurable_right
    {θ₀ : Θ k} {ψ : Θ k → 𝓨 d} {L : 𝓨 d → ℝ≥0∞} (hL_meas : Measurable L)
    (n : ℕ) (h : Θ k) :
    Measurable (lanLoss θ₀ ψ L n h) := by
  unfold lanLoss
  refine hL_meas.comp ?_
  exact (measurable_id.sub_const (ψ (θ₀ + (Real.sqrt n)⁻¹ • h))).const_smul (Real.sqrt n)

/-- Discrete prior `π = ∑_{h ∈ I} π(h) • δ_h` on `Θ k`. -/
noncomputable def discretePrior (I : Finset (Θ k)) (π : Θ k → NNReal) :
    Measure (Θ k) :=
  ∑ h ∈ I, (π h : ℝ≥0∞) • Measure.dirac h

/-- **avgRisk identification** for the LAN setup.

For a kernel `P_n` agreeing with `productMeasure M μ (θ₀ + (√n)⁻¹ • h) n` on the
support `I` of the discrete prior, the average risk under the deterministic
estimator `Kernel.deterministic (T n)` equals the discrete sum
`∑_{h ∈ I} π(h) · ∫⁻ ω, L(√n • (T_n ω - ψ(θ₀+h/√n))) dP_{n,h}(ω)`.

The hypothesis `h_meas_int` is the measurability of the integrand against the
prior coordinate — required for the `lintegral_dirac` step. In practice, this
follows from joint measurability of the integrand-in-`(θ, ω)`, which depends on
how `P_n` is constructed (deferred). -/
lemma avgRisk_lan_discretePrior_eq_sum
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k) (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (ψ : Θ k → 𝓨 d) (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L)
    (I : Finset (Θ k)) (π : Θ k → NNReal)
    (n : ℕ) (P_n : Kernel (Θ k) (Fin n → 𝓧))
    (h_agree : ∀ h ∈ I,
      P_n h = AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (h_meas_int : Measurable
      (fun θ : Θ k => ∫⁻ y, lanLoss θ₀ ψ L n θ y
        ∂(((Kernel.deterministic (T n) (hT_meas n)) ∘ₖ P_n) θ))) :
    avgRisk (lanLoss θ₀ ψ L n) P_n
        (Kernel.deterministic (T n) (hT_meas n)) (discretePrior I π)
      = ∑ h ∈ I, (π h : ℝ≥0∞) *
          ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
                ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) := by
  unfold avgRisk discretePrior
  rw [MeasureTheory.lintegral_finset_sum_measure]
  refine Finset.sum_congr rfl fun h hI => ?_
  rw [MeasureTheory.lintegral_smul_measure, MeasureTheory.lintegral_dirac' h h_meas_int]
  rw [smul_eq_mul]
  congr 1
  have h_comp : ((Kernel.deterministic (T n) (hT_meas n)) ∘ₖ P_n) h
                = (P_n h).map (T n) := by
    rw [Kernel.deterministic_comp_eq_map (hT_meas n) P_n,
        Kernel.map_apply P_n (hT_meas n)]
  rw [h_comp, h_agree h hI]
  rw [MeasureTheory.lintegral_map (lanLoss_measurable_right hL_meas n h) (hT_meas n)]
  rfl

/-- **Bridge: `localAsymptoticRisk` dominates the liminf of LAN Bayes risk**.

For any kernel family `P_n` agreeing with `productMeasure M μ (θ₀ + (√n)⁻¹ • h) n`
on the support of a sub-probability discrete prior, `localAsymptoticRisk`
upper-bounds the liminf of Mathlib's `bayesRisk` along the LAN sequence:

    `liminf_n bayesRisk (lanLoss n) (P_n n) (discretePrior I π)`
    `≤ localAsymptoticRisk M μ θ₀ T ψ L`.

Composes Step A (`localAsymptoticRisk_ge_avg_lower_bound`) with the avgRisk
identification + `bayesRisk_le_avgRisk` for the deterministic estimator
`Kernel.deterministic (T n)`. The discrete-to-Gaussian bridge + Step B
(`bayesRisk` LAN limit) + Step C (Gaussian-shift identification = `bayesRiskAtTau`)
chain on top — this is the link between the Bayesian assembly and Mathlib's
abstract Bayes-risk machinery. -/
lemma localAsymptoticRisk_ge_liminf_lanBayesRisk
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧)
    (θ₀ : Θ k) (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (ψ : Θ k → 𝓨 d) (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L)
    (I : Finset (Θ k)) (π : Θ k → NNReal)
    (hπ_sum : (∑ h ∈ I, (π h : ℝ≥0∞)) ≤ 1)
    (P_n : ∀ n : ℕ, Kernel (Θ k) (Fin n → 𝓧))
    (h_agree : ∀ n : ℕ, ∀ h ∈ I,
      P_n n h = AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (h_meas_int : ∀ n : ℕ, Measurable
      (fun θ : Θ k => ∫⁻ y, lanLoss θ₀ ψ L n θ y
        ∂(((Kernel.deterministic (T n) (hT_meas n)) ∘ₖ P_n n) θ))) :
    Filter.liminf (fun n : ℕ =>
        bayesRisk (lanLoss θ₀ ψ L n) (P_n n) (discretePrior I π)) atTop
      ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
  have h_per_n_bayes : ∀ n,
      bayesRisk (lanLoss θ₀ ψ L n) (P_n n) (discretePrior I π)
        ≤ avgRisk (lanLoss θ₀ ψ L n) (P_n n)
            (Kernel.deterministic (T n) (hT_meas n)) (discretePrior I π) := fun n =>
    bayesRisk_le_avgRisk _ _ _ _
  have h_per_n_eq : ∀ n,
      avgRisk (lanLoss θ₀ ψ L n) (P_n n)
        (Kernel.deterministic (T n) (hT_meas n)) (discretePrior I π)
        = ∑ h ∈ I, (π h : ℝ≥0∞) *
            ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
                  ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) := fun
                      n =>
    avgRisk_lan_discretePrior_eq_sum M μ θ₀ T hT_meas ψ L hL_meas I π n (P_n n)
      (h_agree n) (h_meas_int n)
  have h_per_n :
      ∀ n, bayesRisk (lanLoss θ₀ ψ L n) (P_n n) (discretePrior I π)
        ≤ ∑ h ∈ I, (π h : ℝ≥0∞) *
            ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
                  ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) :=
    fun n => (h_per_n_bayes n).trans_eq (h_per_n_eq n)
  refine (Filter.liminf_le_liminf (Filter.Eventually.of_forall h_per_n)).trans ?_
  exact localAsymptoticRisk_ge_avg_lower_bound M μ θ₀ T ψ L I π hπ_sum

/-! ## Gaussian-shift limit experiment

The "top end" of the Bayesian assembly chain. The bottom end
(`localAsymptoticRisk_ge_liminf_lanBayesRisk`) bridges Step A to
Mathlib `bayesRisk` along the LAN sequence; the top end identifies the
limit Gaussian-shift Bayes risk with `bayesRiskAtTau`. The two links between
them are the LAN-Bayes liminf and the discretization bridge (finite prior →
Gaussian τ-prior). -/

/-- Limit-experiment loss in the Gaussian shift: `(h, y) ↦ L(y - ψDot h)`.
The `y` argument is the estimator output (data lives in `Θ k`, target in `𝓨 d`). -/
noncomputable def lanLossLimit (ψDot : Θ k → 𝓨 d) (L : 𝓨 d → ℝ≥0∞) :
    Θ k → 𝓨 d → ℝ≥0∞ :=
  fun h y => L (y - ψDot h)

/-- Per-`h` measurability of the limit loss as a function of `y`. -/
lemma lanLossLimit_measurable_right
    {ψDot : Θ k → 𝓨 d} {L : 𝓨 d → ℝ≥0∞} (hL_meas : Measurable L)
    (h : Θ k) :
    Measurable (lanLossLimit ψDot L h) := by
  unfold lanLossLimit
  exact hL_meas.comp (measurable_id.sub_const (ψDot h))

/-- Gaussian τ-prior on `Θ k`: `N(0, τ² I)`. -/
noncomputable def gaussianTauPrior (k : ℕ) (τ : ℝ) : Measure (Θ k) :=
  multivariateGaussian 0 ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))

/-- ## **Step C, easy direction — `bayesRisk_∞ π_τ ≤ bayesRiskAtTau`**.

There exists a Markov estimator (the posterior-mean kernel) whose `avgRisk`
under the Gaussian shift τ-prior equals `bayesRiskAtTau J ψDotMat L τ`. By
`bayesRisk ≤ avgRisk` for any Markov κ, the Bayes risk is bounded above.

**Proof sketch**:
1. **Posterior is Gaussian**: For prior `N(0, τ² I)` on `h` and likelihood
   `N(h, J⁻¹)` on `X`, Bayes' rule + complete-the-square gives
   `h | X = x ~ N(posteriorMean(x), posteriorCov)` with
   `posteriorMean(x) := posteriorCov · J · x` and `posteriorCov := (J + (τ²)⁻¹ • I)⁻¹`.
2. **Posterior mean estimator**: Define
   `κ_⋆ := Kernel.deterministic (fun x => ψDot · posteriorMean(x))`. This is
   linear in `x`, hence measurable, hence a Markov kernel by `Kernel.deterministic`.
3. **avgRisk computation**: Under joint `(h ~ π_τ, X | h ~ N(h, J⁻¹))`, the residual
   `h - posteriorMean(X)` has marginal `N(0, posteriorCov)` (conditional Gaussian's
   marginal property). So `ψDot · (h - posteriorMean(X)) ~ N(0, ψDotMat · posteriorCov · ψDotMatᵀ)`.
   Apply `lintegral_map` to identify
   `avgRisk lanLossLimit Plim κ_⋆ π_τ = ∫⁻ y, L y ∂N(0, ψDotMat · posteriorCov · ψDotMatᵀ)
    = bayesRiskAtTau J ψDotMat L τ`.

**Mathlib gaps**: Conditional Gaussian (Bayes posterior of joint Gaussian) is not
in Mathlib. The marginal-of-conditional argument requires Fubini-style integration
against the joint kernel. -/
lemma bayesRisk_gaussianShift_le_bayesRiskAtTau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (ψDot : Θ k → 𝓨 d) (hψDot_meas : Measurable ψDot)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    {τ : ℝ} (hτ : 0 < τ)
    (Plim : Kernel (Θ k) (Θ k))
    (h_Plim_kernel : ∀ h, Plim h = multivariateGaussian h J⁻¹) :
    bayesRisk (lanLossLimit ψDot L) Plim (gaussianTauPrior k τ)
      ≤ GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ := by
  set Sτ := GaussianShiftMinimax.posteriorCov J τ with hSτ_def
  have hSτ_psd : Sτ.PosSemidef :=
    (GaussianShiftMinimax.posteriorCov_posDef hJ hτ).posSemidef
  -- ψDot identifications.
  have h_clm_eq : ∀ g : Θ k, matrixToEuclideanCLMRect ψDotMat g = ψDot g := fun g => by
    rw [h_ψDot_mat g]; rfl
  have h_ψDot_add : ∀ a b : Θ k, ψDot (a + b) = ψDot a + ψDot b := fun a b => by
    have hT_add : matrixToEuclideanCLMRect ψDotMat (a + b)
        = matrixToEuclideanCLMRect ψDotMat a + matrixToEuclideanCLMRect ψDotMat b :=
      map_add _ a b
    rw [h_clm_eq, h_clm_eq, h_clm_eq] at hT_add
    exact hT_add
  -- Posterior-mean estimator κstar as a deterministic Markov kernel.
  have hpm_meas : Measurable (fun x : Θ k => GaussianShiftMinimax.posteriorMean J τ x) := by
    rw [GaussianShiftMinimax.posteriorMean_eq_clm]
    exact (matrixToEuclideanCLMRect _).continuous.measurable
  have hκstar_meas : Measurable
      (fun x : Θ k => ψDot (GaussianShiftMinimax.posteriorMean J τ x)) :=
    hψDot_meas.comp hpm_meas
  let κstar : Kernel (Θ k) (𝓨 d) := Kernel.deterministic
    (fun x => ψDot (GaussianShiftMinimax.posteriorMean J τ x)) hκstar_meas
  haveI hκstar_markov : IsMarkovKernel κstar :=
    Kernel.isMarkovKernel_deterministic hκstar_meas
  -- bayesRisk ≤ avgRisk for κstar (Markov); then avgRisk = bayesRiskAtTau.
  refine le_trans (bayesRisk_le_avgRisk (lanLossLimit ψDot L) Plim κstar
    (gaussianTauPrior k τ)) (le_of_eq ?_)
  -- Innovations rep input function.
  let f : Θ k → Θ k → ℝ≥0∞ := fun h x =>
    L (ψDot (GaussianShiftMinimax.posteriorMean J τ x) - ψDot h)
  have hf_meas : Measurable (Function.uncurry f) := by
    change Measurable
      (fun p : Θ k × Θ k => L (ψDot (GaussianShiftMinimax.posteriorMean J τ p.2) - ψDot p.1))
    have h1 : Measurable (fun p : Θ k × Θ k => ψDot p.1) := hψDot_meas.comp measurable_fst
    have h2 : Measurable
        (fun p : Θ k × Θ k => ψDot (GaussianShiftMinimax.posteriorMean J τ p.2)) :=
      hψDot_meas.comp (hpm_meas.comp measurable_snd)
    exact hL_meas.comp (h2.sub h1)
  have h_innov := GaussianShiftMinimax.gaussianShift_innovations_repr hJ hτ f hf_meas
  -- The pointwise CLM-negation identity: matrixToEuclideanCLMRect (-ψDotMat) g = -(ψDot g).
  have h_clm_neg : ∀ g : Θ k,
      matrixToEuclideanCLMRect (-ψDotMat) g = -(ψDot g) := fun g => by
    apply (WithLp.equiv 2 (Fin d → ℝ)).injective
    rw [WithLp.equiv_apply, WithLp.equiv_apply, WithLp.ofLp_neg,
        ofLp_matrixToEuclideanCLMRect, Matrix.neg_mulVec, ← ofLp_matrixToEuclideanCLMRect,
        h_clm_eq]
  -- Sign cancellation for the covariance: (-A) * S * (-A)ᵀ = A * S * Aᵀ.
  have h_neg_cov : (-ψDotMat) * Sτ * (-ψDotMat).transpose
      = ψDotMat * Sτ * ψDotMat.transpose := by
    rw [Matrix.transpose_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.neg_mul]
    exact neg_neg _
  haveI hπ_X_prob : IsProbabilityMeasure (GaussianShiftMinimax.marginalGaussianShift J τ) := by
    unfold GaussianShiftMinimax.marginalGaussianShift; infer_instance
  -- Main computation: avgRisk = bayesRiskAtTau.
  calc avgRisk (lanLossLimit ψDot L) Plim κstar (gaussianTauPrior k τ)
      = ∫⁻ h, ∫⁻ y, L (y - ψDot h) ∂((κstar ∘ₖ Plim) h) ∂(gaussianTauPrior k τ) := rfl
    _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, L (y - ψDot h) ∂(κstar x) ∂(Plim h) ∂(gaussianTauPrior k τ) := by
        refine lintegral_congr fun h => ?_
        exact Kernel.lintegral_comp κstar Plim h (hL_meas.comp (measurable_id.sub_const _))
    _ = ∫⁻ h, ∫⁻ x, L (ψDot (GaussianShiftMinimax.posteriorMean J τ x) - ψDot h)
            ∂(Plim h) ∂(gaussianTauPrior k τ) := by
        refine lintegral_congr fun h => ?_
        refine lintegral_congr fun x => ?_
        exact Kernel.lintegral_deterministic' hκstar_meas
          (hL_meas.comp (measurable_id.sub_const _))
    _ = ∫⁻ h, ∫⁻ x, f h x ∂(multivariateGaussian h J⁻¹)
            ∂(multivariateGaussian (0 : Θ k) ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))) := by
        refine lintegral_congr fun h => ?_
        rw [h_Plim_kernel h]
    _ = ∫⁻ x, ∫⁻ g, f (g + GaussianShiftMinimax.posteriorMean J τ x) x
            ∂(multivariateGaussian (0 : Θ k) Sτ)
            ∂(GaussianShiftMinimax.marginalGaussianShift J τ) := h_innov
    _ = ∫⁻ x, ∫⁻ g, L (-ψDot g)
            ∂(multivariateGaussian (0 : Θ k) Sτ)
            ∂(GaussianShiftMinimax.marginalGaussianShift J τ) := by
        refine lintegral_congr fun x => ?_
        refine lintegral_congr fun g => ?_
        change L (ψDot (GaussianShiftMinimax.posteriorMean J τ x)
              - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x)) = L (-ψDot g)
        congr 1
        rw [h_ψDot_add g (GaussianShiftMinimax.posteriorMean J τ x)]
        abel
    _ = ∫⁻ g, L (-ψDot g) ∂(multivariateGaussian (0 : Θ k) Sτ) := by
        rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ g, L (matrixToEuclideanCLMRect (-ψDotMat) g)
            ∂(multivariateGaussian (0 : Θ k) Sτ) := by
        refine lintegral_congr fun g => ?_; rw [h_clm_neg]
    _ = ∫⁻ y, L y
            ∂((multivariateGaussian (0 : Θ k) Sτ).map
              (matrixToEuclideanCLMRect (-ψDotMat))) := by
        exact (lintegral_map hL_meas
          (matrixToEuclideanCLMRect (-ψDotMat)).continuous.measurable).symm
    _ = ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
            ((-ψDotMat) * Sτ * (-ψDotMat).transpose)) := by
        rw [multivariateGaussian_map_rectangular (-ψDotMat) 0 hSτ_psd]
        rw [show (matrixToEuclideanCLMRect (-ψDotMat) (0 : Θ k)) = (0 : 𝓨 d) from
          (matrixToEuclideanCLMRect (-ψDotMat)).map_zero]
    _ = ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
            (ψDotMat * Sτ * ψDotMat.transpose)) := by
        rw [h_neg_cov]
    _ = GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ := rfl

/-- ## **Step C, hard direction — substantive per-estimator inequality.**

**Black-box gap (substantive content of Step C HARD).** For ANY Markov estimator
`κ : Kernel (Θ k) (𝓨 d)`, its average risk under the Gaussian-shift τ-prior
dominates `bayesRiskAtTau`:
`bayesRiskAtTau J ψDotMat L τ ≤ avgRisk (lanLossLimit ψDot L) Plim κ π_τ`.

This is the **substantive Bayesian-decision-theoretic content** of Step C HARD;
the wrapping `bayesRiskAtTau_le_bayesRisk_gaussianShift` then closes by
`bayesRisk = ⨅ κ markov, avgRisk` and `le_iInf₂`.

**Mathematical proof** (Bayesian-Gaussian infrastructure not in Mathlib):

1. **Innovations representation** (the load-bearing Mathlib gap). Under joint
   `(h, X) ~ π_τ ⊗ Plim`, the random variable `g := h - posteriorCov · J · X`
   has marginal `N(0, posteriorCov)` AND is **independent of X**. The marginal
   of `X` is `π_X := N(0, J⁻¹ + τ²·I)`. Hence
   `∫⁻ h ∂π_τ ∫⁻ x ∂Plim(h) F(h,x) = ∫⁻ x ∂π_X ∫⁻ g ∂N(0, posteriorCov)
       F(g + posteriorCov·J·x, x)`
   for measurable `F`. **Requires** Mathlib infrastructure for joint Gaussian
   conjugation / Bayes posterior identification, which does not exist.
2. **Linear pushforward of Gaussian** (rectangular case). For S PSD on `Θ k`
   and `ψDotMat : Matrix d k`,
   `∫⁻ g, L(c - ψDotMat g) ∂N(0, S) = ∫⁻ z, L(c - z) ∂N(0, ψDotMat · S · ψDotMatᵀ)`.
   Mathlib has the square version
   (`multivariateGaussian_map_toEuclideanCLM` in `ForMathlib/GaussianMGF.lean`);
   the rectangular version is a parallel ~50-100 line proof via `IsGaussian.ext`.
3. **Anderson loss form** (`anderson_lemma_loss`, ✅ closed): for any shift `c`,
   `∫⁻ z, L z ∂N(0, S) ≤ ∫⁻ z, L(z + c) ∂N(0, S)`. Combined with bowl-shape
   symmetry `L(c - z) = L(z - c)` and the c → -c substitution, gives
   `bayesRiskAtTau ≤ ∫⁻ z, L(c - z) ∂N(0, ψDotMat · posteriorCov · ψDotMatᵀ)`.
4. **Outer collapse**. Both `κ` Markov and `π_X` probability measure, so
   `∫⁻ x ∂π_X, ∫⁻ y ∂κ(x), bayesRiskAtTau = bayesRiskAtTau · 1 · 1`.

Together: `avgRisk = (1) ≥ (3) = ∫…∫ bayesRiskAtTau = (4) bayesRiskAtTau`. -/
private lemma avgRisk_gaussianShift_ge_bayesRiskAtTau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (ψDot : Θ k → 𝓨 d) (hψDot_meas : Measurable ψDot)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_bowl : BowlShaped L)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    {τ : ℝ} (hτ : 0 < τ)
    (Plim : Kernel (Θ k) (Θ k))
    (h_Plim_kernel : ∀ h, Plim h = multivariateGaussian h J⁻¹)
    (κ : Kernel (Θ k) (𝓨 d)) (_hκ : IsMarkovKernel κ) :
    GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
      ≤ avgRisk (lanLossLimit ψDot L) Plim κ (gaussianTauPrior k τ) := by
  -- Setup notation.
  set Sτ := GaussianShiftMinimax.posteriorCov J τ with hSτ_def
  set covLink := ψDotMat * Sτ * ψDotMat.transpose with hCovLink_def
  -- PSD facts.
  have hSτ_psd : Sτ.PosSemidef :=
    (GaussianShiftMinimax.posteriorCov_posDef hJ hτ).posSemidef
  have hCovLink_psd : covLink.PosSemidef := by
    change (ψDotMat * Sτ * ψDotMat.transpose).PosSemidef
    have := hSτ_psd.mul_mul_conjTranspose_same ψDotMat
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  -- `matrixToEuclideanCLMRect ψDotMat g = ψDot g` (definitional, via `h_ψDot_mat`).
  have h_clm_eq : ∀ g : Θ k, matrixToEuclideanCLMRect ψDotMat g = ψDot g := fun g => by
    rw [h_ψDot_mat g]; rfl
  -- ψDot is linear via the underlying CLM: ψDot (a + b) = ψDot a + ψDot b.
  have h_ψDot_add : ∀ a b : Θ k, ψDot (a + b) = ψDot a + ψDot b := fun a b => by
    have hT_add : matrixToEuclideanCLMRect ψDotMat (a + b)
        = matrixToEuclideanCLMRect ψDotMat a + matrixToEuclideanCLMRect ψDotMat b :=
      map_add _ a b
    rw [h_clm_eq] at hT_add
    rw [h_clm_eq] at hT_add
    rw [h_clm_eq] at hT_add
    exact hT_add
  -- Inner bound: for each (x, y), `bayesRiskAtTau ≤ ∫⁻ g, L(y - ψDot(g + posteriorMean(x)))`.
  -- Proof: Anderson translation + reverse rectangular Gaussian pushforward + ψDot linearity.
  have h_inner_ge : ∀ (x : Θ k) (y : 𝓨 d),
      GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
        ≤ ∫⁻ g, L (y - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x))
            ∂(multivariateGaussian (0 : Θ k) Sτ) := by
    intro x y
    set c := y - ψDot (GaussianShiftMinimax.posteriorMean J τ x) with hc_def
    -- ψDot linearity rewrites the integrand: `y - ψDot(g + e) = c - ψDot g`.
    have h_split : ∀ g : Θ k,
        y - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x) = c - ψDot g := fun g => by
      rw [h_ψDot_add g (GaussianShiftMinimax.posteriorMean J τ x), hc_def]; abel
    -- Chain: bayesRiskAtTau = ∫⁻ z, L z ∂N(0, covLink)
    --     ≤ ∫⁻ z, L(c-z) ∂N(0, covLink)                    [Anderson translation]
    --     = ∫⁻ z, L(c-z) ∂((N(0,Sτ)).map T)                [rect pushforward, reversed]
    --     = ∫⁻ g, L(c - T g) ∂N(0, Sτ)                     [lintegral_map]
    --     = ∫⁻ g, L(c - ψDot g) ∂N(0, Sτ)                  [h_clm_eq]
    --     = ∫⁻ g, L(y - ψDot(g + posteriorMean(x))) ∂N(0, Sτ)  [h_split, reversed]
    -- where T := matrixToEuclideanCLMRect ψDotMat.
    calc GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
        = ∫⁻ z, L z ∂(multivariateGaussian (0 : 𝓨 d) covLink) := rfl
      _ ≤ ∫⁻ z, L (c - z) ∂(multivariateGaussian (0 : 𝓨 d) covLink) :=
            lintegral_loss_translated_ge hCovLink_psd hL_bowl c
      _ = ∫⁻ z, L (c - z) ∂((multivariateGaussian (0 : Θ k) Sτ).map
              (matrixToEuclideanCLMRect ψDotMat)) := by
            rw [multivariateGaussian_map_rectangular ψDotMat 0 hSτ_psd]
            -- `matrixToEuclideanCLMRect ψDotMat 0 = 0` by linearity.
            rw [show (matrixToEuclideanCLMRect ψDotMat (0 : Θ k)) = (0 : 𝓨 d) from
              (matrixToEuclideanCLMRect ψDotMat).map_zero]
      _ = ∫⁻ g, L (c - matrixToEuclideanCLMRect ψDotMat g)
              ∂(multivariateGaussian 0 Sτ) := by
            have hF_meas : Measurable (fun z : 𝓨 d => L (c - z)) := by fun_prop
            have hT_meas : Measurable (matrixToEuclideanCLMRect ψDotMat) :=
              (matrixToEuclideanCLMRect ψDotMat).continuous.measurable
            exact lintegral_map hF_meas hT_meas
      _ = ∫⁻ g, L (c - ψDot g) ∂(multivariateGaussian 0 Sτ) := by
            refine lintegral_congr fun g => ?_; rw [h_clm_eq]
      _ = ∫⁻ g, L (y - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x))
              ∂(multivariateGaussian 0 Sτ) := by
            refine lintegral_congr fun g => ?_; rw [h_split]
  -- Outer step: combine via outer probability collapse + Fubini swap + innovations rep
  -- + `Plim → mvg` + `Kernel.lintegral_comp` to reach the avgRisk form.
  -- π_X is the marginal of X under the joint experiment.
  set π_X := GaussianShiftMinimax.marginalGaussianShift J τ with hπ_X_def
  -- π_X is a probability measure (multivariateGaussian on a PSD matrix).
  haveI hπ_X_prob : IsProbabilityMeasure π_X := by
    rw [hπ_X_def, GaussianShiftMinimax.marginalGaussianShift]; infer_instance
  -- Joint integrand `finn h x := ∫⁻ y, L(y - ψDot h) ∂(κ x)` is measurable on `Θk × Θk`.
  let finn : Θ k → Θ k → ℝ≥0∞ := fun h x => ∫⁻ y, L (y - ψDot h) ∂(κ x)
  have hfinn_uncurry_meas : Measurable (Function.uncurry finn) := by
    -- Build a kernel `κ' : Kernel (Θk × Θk) (𝓨d)` via `comap` with `Prod.snd`.
    let snd : Θ k × Θ k → Θ k := Prod.snd
    have hsnd_meas : Measurable snd := measurable_snd
    let κ' : Kernel (Θ k × Θ k) (𝓨 d) := κ.comap snd hsnd_meas
    haveI hκ'_markov : IsMarkovKernel κ' := Kernel.IsMarkovKernel.comap κ hsnd_meas
    have h_int_meas : Measurable
        (fun p : (Θ k × Θ k) × 𝓨 d => L (p.2 - ψDot p.1.1)) := by fun_prop
    have h_main : Measurable
        (fun p : Θ k × Θ k => ∫⁻ y, L (y - ψDot p.1) ∂(κ' p)) :=
      Measurable.lintegral_kernel_prod_right' (κ := κ') h_int_meas
    -- `κ' p = κ p.2` by `Kernel.comap_apply`, definitionally — so `convert` closes.
    convert h_main using 1
  -- Outer chain: bayesRiskAtTau ≤ … = avgRisk.
  calc GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
      = ∫⁻ x, ∫⁻ _y : 𝓨 d, GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
              ∂(κ x) ∂π_X := by
        -- Outer collapse: `c = ∫⁻ x ∂π_X, ∫⁻ y ∂(κ x), c` (π_X prob + κ Markov).
        have h_inner : ∀ x, ∫⁻ _y : 𝓨 d,
            GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ ∂(κ x)
              = GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ := fun x => by
          rw [lintegral_const, measure_univ, mul_one]
        simp_rw [h_inner]
        rw [lintegral_const, measure_univ, mul_one]
    _ ≤ ∫⁻ x, ∫⁻ y, ∫⁻ g, L (y - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x))
            ∂(multivariateGaussian (0 : Θ k) Sτ) ∂(κ x) ∂π_X := by
        refine lintegral_mono fun x => ?_
        refine lintegral_mono fun y => ?_
        exact h_inner_ge x y
    _ = ∫⁻ x, ∫⁻ g, ∫⁻ y, L (y - ψDot (g + GaussianShiftMinimax.posteriorMean J τ x))
            ∂(κ x) ∂(multivariateGaussian (0 : Θ k) Sτ) ∂π_X := by
        -- Fubini swap g ↔ y inside the x-integral.
        refine lintegral_congr fun x => ?_
        refine MeasureTheory.lintegral_lintegral_swap ?_
        refine Measurable.aemeasurable ?_
        fun_prop
    _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, L (y - ψDot h) ∂(κ x) ∂(multivariateGaussian h J⁻¹)
            ∂(multivariateGaussian (0 : Θ k) ((τ^2) • (1 : Matrix (Fin k) (Fin k) ℝ))) := by
        -- Apply `gaussianShift_innovations_repr` reversed: LHS = innovations RHS = our previous
        -- form.
        exact (GaussianShiftMinimax.gaussianShift_innovations_repr
          hJ hτ finn hfinn_uncurry_meas).symm
    _ = ∫⁻ h, ∫⁻ x, ∫⁻ y, L (y - ψDot h) ∂(κ x) ∂(Plim h)
            ∂(gaussianTauPrior k τ) := by
        -- Substitute `multivariateGaussian h J⁻¹ = Plim h` (reverse h_Plim_kernel)
        -- and `gaussianTauPrior = multivariateGaussian 0 ((τ²)•1)`.
        refine lintegral_congr fun h => ?_
        rw [← h_Plim_kernel h]
    _ = ∫⁻ h, ∫⁻ y, L (y - ψDot h) ∂((κ ∘ₖ Plim) h) ∂(gaussianTauPrior k τ) := by
        -- Reverse `Kernel.lintegral_comp`.
        refine lintegral_congr fun h => ?_
        exact (Kernel.lintegral_comp κ Plim h
          (hL_meas.comp (measurable_id.sub_const _))).symm
    _ = avgRisk (lanLossLimit ψDot L) Plim κ (gaussianTauPrior k τ) := rfl

/-- ## **Step C, hard direction (Anderson) — `bayesRiskAtTau ≤ bayesRisk_∞ π_τ`**.

No estimator beats the posterior-mean estimator's avgRisk. For bowl-shaped `L`,
Anderson's PSD-monotone form on the Gaussian posterior says: for ANY estimator
`κ : Kernel (Θ k) (𝓨 d)`, the conditional risk
`E[L(ψDot h - κ(X)) | X = x]` is minimized when `κ(x) = ψDot · posteriorMean(x)`,
giving the explicit value `∫⁻ y, L y ∂N(0, ψDotMat · posteriorCov · ψDotMatᵀ)`.
Marginalizing over `X` preserves this lower bound.

**This is the load-bearing direction in the 8.11 chain** — it's what gives
`bayesRiskAtTau ≤ localAsymptoticRisk` after composition with the bridge and
the LAN-Bayes limit.

**Wrapper structure**: `bayesRisk = ⨅ κ markov, avgRisk` (Mathlib def);
combined with `avgRisk_gaussianShift_ge_bayesRiskAtTau` (the substantive
per-estimator inequality) via `le_iInf₂`, the result follows. The substantive
content lives in `avgRisk_gaussianShift_ge_bayesRiskAtTau`. -/
lemma bayesRiskAtTau_le_bayesRisk_gaussianShift
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (ψDot : Θ k → 𝓨 d) (hψDot_meas : Measurable ψDot)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_bowl : BowlShaped L)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    {τ : ℝ} (hτ : 0 < τ)
    (Plim : Kernel (Θ k) (Θ k))
    (h_Plim_kernel : ∀ h, Plim h = multivariateGaussian h J⁻¹) :
    GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ
      ≤ bayesRisk (lanLossLimit ψDot L) Plim (gaussianTauPrior k τ) := by
  -- `bayesRisk = ⨅ κ markov, avgRisk`. Take `le_iInf₂` and reduce to the
  -- per-estimator inequality `avgRisk_gaussianShift_ge_bayesRiskAtTau`.
  refine le_iInf₂ fun κ hκ => ?_
  exact avgRisk_gaussianShift_ge_bayesRiskAtTau hJ ψDot hψDot_meas L hL_meas hL_bowl
    ψDotMat h_ψDot_mat hτ Plim h_Plim_kernel κ hκ

/-- ## **Gaussian-shift Bayes risk = `bayesRiskAtTau`**.

For the limit Gaussian-shift experiment with prior `π_τ = N(0, τ² I)` on `Θ k`,
data kernel `Plim : h ↦ N(h, J⁻¹)`, linear target `A h = ψDotMat · h`, and
bowl-shaped loss `L`, the Mathlib `bayesRisk` of the loss `lanLossLimit ψDot L`
equals the explicit form `bayesRiskAtTau J ψDotMat L τ`.

**Composition**: `le_antisymm` of:
- `bayesRisk_gaussianShift_le_bayesRiskAtTau` (easy, posterior-mean achieves)
- `bayesRiskAtTau_le_bayesRisk_gaussianShift` (hard, Anderson optimality)

**Position in the assembly**: This is the **top end** of the chain
`localAsymptoticRisk ≥ liminf bayesRisk_n ≥ bayesRisk_∞ π_τ = bayesRiskAtTau`.
The chain only uses the **hard direction** (`≤`); the equality wrapper here is
mathematically pleasing but the easy direction is not load-bearing for 8.11. -/
lemma bayesRisk_gaussianShift_eq_bayesRiskAtTau
    {J : Matrix (Fin k) (Fin k) ℝ} (hJ : J.PosDef)
    (ψDot : Θ k → 𝓨 d) (hψDot_meas : Measurable ψDot)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_bowl : BowlShaped L)
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    {τ : ℝ} (hτ : 0 < τ)
    (Plim : Kernel (Θ k) (Θ k))
    (h_Plim_kernel : ∀ h, Plim h = multivariateGaussian h J⁻¹) :
    bayesRisk (lanLossLimit ψDot L) Plim (gaussianTauPrior k τ)
      = GaussianShiftMinimax.bayesRiskAtTau J ψDotMat L τ :=
  le_antisymm
    (bayesRisk_gaussianShift_le_bayesRiskAtTau hJ ψDot hψDot_meas L hL_meas
      ψDotMat h_ψDot_mat hτ Plim h_Plim_kernel)
    (bayesRiskAtTau_le_bayesRisk_gaussianShift hJ ψDot hψDot_meas L hL_meas hL_bowl
      ψDotMat h_ψDot_mat hτ Plim h_Plim_kernel)


/-- **Joint measurability of the LAN integrand in `h`.**

Per-`h` measurability of the inner integrand `fun y => L(y - ψDot h)` lifted to
a joint `(h, integrand)` measurable form, needed for the per-`n`
`bayesRisk = ∫⁻ y, ⨅ b, ...` representation along the discrete prior. -/
private theorem lanIntegrand_measurable_in_h
    (_θ₀ : EuclideanSpace ℝ (Fin k)) (ψDot : EuclideanSpace ℝ (Fin k) →L[ℝ] 𝓨 d)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L)
    (_n : ℕ) :
    Measurable
      (fun h : EuclideanSpace ℝ (Fin k) =>
        fun y : 𝓨 d => L (y - ψDot h)) := by
  -- The codomain `𝓨 d → ℝ≥0∞` is a Pi-type with the product measurable
  -- space: a map into it is measurable iff its evaluation at every `y` is.
  refine measurable_pi_lambda _ ?_
  intro y
  -- Per-`y`: `fun h => L (y - ψDot h)` is `L ∘ (y - ψDot ·)`, which is
  -- measurable since `L` is measurable and `(fun h => y - ψDot h)` is
  -- measurable (continuous: continuous-const minus continuous-linear-map).
  refine hL_meas.comp ?_
  exact (measurable_const.sub ψDot.continuous.measurable)



/-! ## vdV §8.11 direct proof path

The direct vdV §8.11 proof path: joint tightness of `(√n(T_n - ψθ₀), score sum)`
under `P^n_θ₀`, Prokhorov subsequence + Le Cam shift via score CLT, lsc-Portmanteau
on the limit Gaussian-shift integrand, rational sup-lift to recover the original
`localAsymptoticRisk` from a countable approximation. The sub-lemmas are:

* `joint_tightness_T_score_under_P_theta0` — joint tightness of the
  estimator-and-score pair under the central measure. `hTight` (vdV §8.11)
  is the marginal-T half; the score-side tightness comes from
  `scoreSum_weakly_converges` (CLT-tight). Joint tightness =
  Mathlib `IsTightMeasureSet` of the product pushforward measure family.
* `Eh_loss_lsc_in_shift` — lsc of `h̃ ↦ ∫⁻ L(y) d(mvg h̃ Σ)` in the
  shift parameter (vdV §8.5), used in the limit-side Portmanteau step.
  Composes shift-continuity of `multivariateGaussian` with lsc Portmanteau.
* `iSup_finite_le_iSup_rational_finite_via_lsc` — rational sup lift. Replaces
  `⨆ I : Finset (ℝ^k)` with `⨆ I : Finset (rationals)` on lsc integrands,
  reducing the outer uncountable sup to a countable one (density argument).
* `localAsymptoticRisk_ge_target` — the main chain, with the same
  conclusion as `local_asymptotic_minimax_bound`.

Shift-continuity of `multivariateGaussian h Σ` in `h` is provided by
`multivariateGaussian_kernel_Feller`. -/

/-- **Helper: Fisher information matrix is PSD.**

The bilinear form `(u, v) ↦ fisherInformation M μ θ₀ ℓ u v` is the L²(p_θ dμ)
Gram form of the linear maps `u ↦ ⟨u, ℓ⟩`; hence symmetric and PSD as a Gram
matrix. The matrix `J` representing it in the standard basis inherits both
properties.

Proof: `Matrix.posSemidef_iff_dotProduct_mulVec` reduces to (a) `J.IsHermitian`
+ (b) `0 ≤ x ⬝ᵥ J.mulVec x` for `x : Fin k → ℝ`. For (b), via `hJ_fisher` and
the `WithLp.equiv`/`PiLp.inner_apply` bridge, `x ⬝ᵥ J.mulVec x` equals
`fisherInformation M μ θ₀ ℓ u u = ∫ ⟨u, ℓ⟩² · p_{θ₀} ≥ 0` where `u =
(WithLp.equiv 2 _).symm x`. For (a), the same equality applied to standard
basis pairs `(e_i, e_j)` gives `J i j = fisher e_i e_j = fisher e_j e_i =
J j i`. -/
theorem J_posSemidef_of_fisher_eq
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫) :
    J.PosSemidef := by
  classical
  -- The bridge: `⟪u, J.mulVec_with_lift v⟫ = u.ofLp ⬝ᵥ J.mulVec v.ofLp`.
  have inner_bridge : ∀ u v : EuclideanSpace ℝ (Fin k),
      ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫
        = u.ofLp ⬝ᵥ J.mulVec v.ofLp := by
    intro u v
    rw [show (u.ofLp ⬝ᵥ J.mulVec v.ofLp) = ∑ i, u.ofLp i * (J.mulVec v.ofLp) i from rfl]
    simp only [PiLp.inner_apply, WithLp.equiv_apply, WithLp.equiv_symm_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    change (J.mulVec v.ofLp) i * u.ofLp i = u.ofLp i * (J.mulVec v.ofLp) i
    ring
  -- Fisher info is symmetric in (u, v).
  have fisher_symm : ∀ u v : Θ k,
      fisherInformation M μ θ₀ ℓ u v = fisherInformation M μ θ₀ ℓ v u := by
    intro u v
    unfold fisherInformation
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  -- Fisher info is nonneg on the diagonal.
  have fisher_nonneg : ∀ u : Θ k, 0 ≤ fisherInformation M μ θ₀ ℓ u u := by
    intro u
    unfold fisherInformation
    refine integral_nonneg (fun x => ?_)
    have h_dens : 0 ≤ M.density θ₀ x := M.density_nonneg θ₀ x
    have h_sq : 0 ≤ ⟪u, ℓ x⟫ * ⟪u, ℓ x⟫ := mul_self_nonneg _
    exact mul_nonneg h_sq h_dens
  -- Bridge: define `lift x` as the EuclideanSpace vector with components x.
  -- `(WithLp.equiv 2 _).symm x` and `(lift x).ofLp = x` by structure projection.
  have lift_ofLp : ∀ x : Fin k → ℝ,
      ((WithLp.equiv 2 (Fin k → ℝ)).symm x).ofLp = x := fun x => rfl
  -- Step 1: J.IsHermitian. Over ℝ, `Jᴴ = Jᵀ` and we want `Jᵀ = J`, i.e. `J i j = J j i`.
  have hHermitian : J.IsHermitian := by
    refine Matrix.IsHermitian.ext (fun i j => ?_)
    -- Compute `dotProduct (Pi.single i 1) (J.mulVec (Pi.single j 1)) = J i j`.
    have h_single : ∀ a b : Fin k,
        (Pi.single a (1 : ℝ)) ⬝ᵥ J.mulVec (Pi.single b 1) = J a b := by
      intro a b
      simp [dotProduct, Matrix.mulVec, Pi.single_apply, Finset.sum_ite_eq']
    have h_ij : J i j = fisherInformation M μ θ₀ ℓ
        ((WithLp.equiv 2 (Fin k → ℝ)).symm (Pi.single i 1))
        ((WithLp.equiv 2 (Fin k → ℝ)).symm (Pi.single j 1)) := by
      rw [hJ_fisher, inner_bridge, lift_ofLp, lift_ofLp, h_single]
    have h_ji : J j i = fisherInformation M μ θ₀ ℓ
        ((WithLp.equiv 2 (Fin k → ℝ)).symm (Pi.single j 1))
        ((WithLp.equiv 2 (Fin k → ℝ)).symm (Pi.single i 1)) := by
      rw [hJ_fisher, inner_bridge, lift_ofLp, lift_ofLp, h_single]
    -- Hermitian over ℝ: J^conjTranspose i j = star (J j i) = J j i = J i j.
    change star (J j i) = J i j
    rw [star_trivial, h_ji, h_ij, fisher_symm]
  -- Step 2: quadratic form nonneg.
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨hHermitian, fun x => ?_⟩
  -- Over ℝ, star x = x; so the goal is `0 ≤ x ⬝ᵥ J.mulVec x`.
  have h_star : (star x : Fin k → ℝ) = x := by funext i; exact star_trivial _
  rw [h_star]
  -- Set u := (WithLp.equiv 2 _).symm x; then via inner_bridge and hJ_fisher,
  -- x ⬝ᵥ J.mulVec x = fisher u u ≥ 0.
  set u : EuclideanSpace ℝ (Fin k) := (WithLp.equiv 2 _).symm x with hu_def
  have h_quad : x ⬝ᵥ J.mulVec x = fisherInformation M μ θ₀ ℓ u u := by
    have := inner_bridge u u
    rw [lift_ofLp] at this
    rw [← this]
    exact (hJ_fisher u u).symm
  rw [h_quad]
  exact fisher_nonneg u

/-- **Joint tightness of `(√n (T_n - ψ θ₀), score sum_n)` under `P^n_θ₀`.**

vdV §8.11 step 1 uses joint tightness of the estimator-score pair on the LAN
side as the bridge between LAN expansion (Theorem 7.2 (iii)) and the limit
Gaussian-shift experiment. The marginal-`T` half is supplied by `hTight`
(vdV §8.11); the score-side tightness follows from `scoreSum_weakly_converges`
(CLT under `P^n_θ₀`).

Closed via the Prohorov product (`tight_prod_of_tight_marginals`):
* T-marginal: `Measure.map_map` collapses `(map (T̃ × Δ)).map fst = map T̃`,
  reducing to `hTight`.
* Score-marginal: `scoreSum_weakly_converges` (Theorem 7.10 brick) + Prohorov
  converse `weakConverges_range_tight`.
* `J.PosSemidef` is delegated to `J_posSemidef_of_fisher_eq`. -/
theorem joint_tightness_T_score_under_P_theta0
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    -- sequence `√n (T_n - ψ θ₀)` is uniformly tight under `P^n_θ₀`. This is
    -- the **consistency hypothesis** vdV makes verbatim at the head of §8.11.
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ) :
    MeasureTheory.IsTightMeasureSet
      (Set.range (fun n : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ((Real.sqrt n) • (T n ω - ψ θ₀),
                     AsymptoticRepresentation.scoreSum ℓ n ω)))) := by
  classical
  -- IsProbabilityMeasure instances for each productMeasure and the limit mvg.
  haveI : ∀ n, IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ₀ n) :=
    fun n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ₀ n
  -- The joint pushforward set.
  set S : Set (Measure (𝓨 d × Θ k)) := Set.range (fun n : ℕ =>
    (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
      (fun ω => ((Real.sqrt n) • (T n ω - ψ θ₀), AsymptoticRepresentation.scoreSum ℓ n ω))) with
          hS_def
  -- Measurability of the joint pushforward function for each n.
  have h_T_n_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      (Real.sqrt n) • (T n ω - ψ θ₀)) := fun n =>
    ((hT_meas n).sub_const _).const_smul (Real.sqrt n)
  have h_score_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := fun n => by
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_pair_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      ((Real.sqrt n) • (T n ω - ψ θ₀), AsymptoticRepresentation.scoreSum ℓ n ω)) :=
    fun n => (h_T_n_meas n).prodMk (h_score_meas n)
  -- Apply Prohorov product: marginal tight ⇒ joint tight.
  refine AsymptoticStatistics.Prohorov.tight_prod_of_tight_marginals S ?_ ?_
  · -- T-marginal: the image of S under `Prod.fst` push equals `hTight`'s set.
    have h_T_image :
        (fun ν : Measure (𝓨 d × Θ k) => ν.map Prod.fst) '' S =
          Set.range (fun n : ℕ =>
            (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
              (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀))) := by
      ext ρ
      simp only [Set.mem_image, Set.mem_range, hS_def]
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        refine ⟨n, ?_⟩
        rw [Measure.map_map measurable_fst (h_pair_meas n)]
        rfl
      · rintro ⟨n, rfl⟩
        refine ⟨_, ⟨n, rfl⟩, ?_⟩
        rw [Measure.map_map measurable_fst (h_pair_meas n)]
        rfl
    rw [h_T_image]
    exact hTight
  · -- Score-marginal: weak convergence to multivariateGaussian 0 J + Prohorov converse.
    have hJ_psd : J.PosSemidef :=
      J_posSemidef_of_fisher_eq M μ θ₀ ℓ J hJ_fisher
    have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
    have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
    have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k,
        ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
      fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
    have hint_perturb : ∀ t : ℝ, ∀ u : Θ k,
        Integrable (M.density (θ₀ + t • u)) μ :=
      fun t u => hPDF.density_integrable (θ₀ + t • u)
    have h_score_weak :
        WeakConverges (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n))
          (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
      AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint
        h_one_perturb hint_perturb hDQM J hJ_psd hJ_fisher
    have h_score_image :
        (fun ν : Measure (𝓨 d × Θ k) => ν.map Prod.snd) '' S =
          Set.range (fun n : ℕ =>
            (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
              (AsymptoticRepresentation.scoreSum ℓ n)) := by
      ext ρ
      simp only [Set.mem_image, Set.mem_range, hS_def]
      constructor
      · rintro ⟨ν, ⟨n, rfl⟩, rfl⟩
        refine ⟨n, ?_⟩
        rw [Measure.map_map measurable_snd (h_pair_meas n)]
        rfl
      · rintro ⟨n, rfl⟩
        refine ⟨_, ⟨n, rfl⟩, ?_⟩
        rw [Measure.map_map measurable_snd (h_pair_meas n)]
        rfl
    rw [h_score_image]
    -- IsProbabilityMeasure on each score pushforward (map of a probability under measurable).
    haveI : ∀ n, IsProbabilityMeasure
        ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map (AsymptoticRepresentation.scoreSum ℓ
            n)) :=
      fun n => MeasureTheory.Measure.isProbabilityMeasure_map (h_score_meas n).aemeasurable
    -- multivariateGaussian is a probability measure (unconditional via IsGaussian).
    haveI : IsProbabilityMeasure (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
      inferInstance
    exact AsymptoticStatistics.Prohorov.weakConverges_range_tight
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J)
      h_score_weak

/-- **Lower semicontinuity of `h̃ ↦ ∫⁻ L(y) ∂(mvg h̃ Σ)` in the shift.**

vdV §8.5: the limit-side Bayes integrand against the shifted Gaussian is lsc in
the shift parameter, used inside the lsc-Portmanteau step that closes the limit
side of the proof.

Composes the shift-continuity of `multivariateGaussian h Σ` in `h`
(`multivariateGaussian_kernel_Feller`) with the lsc-Portmanteau bridge. -/
theorem Eh_loss_lsc_in_shift
    {d : ℕ} (S : Matrix (Fin d) (Fin d) ℝ) (_hS : S.PosSemidef)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L) :
    LowerSemicontinuous (fun htil : 𝓨 d =>
      ∫⁻ y, L (y - htil) ∂(multivariateGaussian (0 : 𝓨 d) S)) := by
  -- Abbreviate the parameterised integral.
  set ν : Measure (𝓨 d) := multivariateGaussian (0 : 𝓨 d) S with hν_def
  set F : 𝓨 d → ℝ≥0∞ := fun htil => ∫⁻ y, L (y - htil) ∂ν with hF_def
  -- For each fixed `z`, `h ↦ L(z - h)` is lsc (composition of lsc and continuous).
  have hL_shift_lsc : ∀ z : 𝓨 d, LowerSemicontinuous (fun h : 𝓨 d => L (z - h)) := by
    intro z
    exact hL_lsc.comp (continuous_const.sub continuous_id)
  -- Measurability of `y ↦ L(y - htil)` for each `htil`, needed for Fatou.
  have hL_shift_meas : ∀ htil : 𝓨 d, Measurable (fun y : 𝓨 d => L (y - htil)) := by
    intro htil
    exact hL_meas.comp (measurable_id.sub_const htil)
  -- Reduce to closed-sublevel-set criterion (`ℝ≥0∞` is a linear order).
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr ?_
  intro c
  -- `𝓨 d = EuclideanSpace ℝ (Fin d)` is metrisable hence a `SequentialSpace`;
  -- a set is closed iff it is sequentially closed.
  refine isSeqClosed_iff_isClosed.mp ?_
  intro htil_seq htil h_mem h_tend
  -- `h_mem n : F (htil_seq n) ≤ c`; `h_tend : Tendsto htil_seq atTop (𝓝 htil)`.
  -- Goal after unfolding membership: `F htil ≤ c`.
  change F htil ≤ c
  -- Step 1: pointwise sequential lsc — for each `z`, `L(z - htil) ≤ liminf_n L(z - htil_seq n)`.
  have h_pt : ∀ y : 𝓨 d,
      L (y - htil) ≤ Filter.atTop.liminf (fun n => L (y - htil_seq n)) := by
    intro y
    -- `hL_shift_lsc y` gives `(fun h => L(y - h)) h ≤ liminf (fun h => L(y - h)) (𝓝 h)` for any h.
    have h_lsc_y : LowerSemicontinuous (fun h : 𝓨 d => L (y - h)) := hL_shift_lsc y
    have h_filter : L (y - htil) ≤ Filter.liminf (fun h : 𝓨 d => L (y - h)) (𝓝 htil) :=
      h_lsc_y.le_liminf htil
    -- Push from filter `𝓝 htil` along the sequence: `map htil_seq atTop ≤ 𝓝 htil`.
    refine h_filter.trans ?_
    have hmap : Filter.map htil_seq Filter.atTop ≤ 𝓝 htil := h_tend
    have h_le := Filter.liminf_le_liminf_of_le (β := ℝ≥0∞)
      (u := fun h : 𝓨 d => L (y - h)) hmap
    -- `liminf (fun h => L(y-h)) (map htil_seq atTop) = liminf (fun n => L(y - htil_seq n)) atTop`.
    have h_rewrite :
        Filter.liminf (fun h : 𝓨 d => L (y - h)) (Filter.map htil_seq Filter.atTop)
          = Filter.atTop.liminf (fun n => L (y - htil_seq n)) := by
      simp [Filter.liminf, Filter.limsInf, Filter.map_map, Function.comp]
    rw [h_rewrite] at h_le
    exact h_le
  -- Step 2: Fatou (sequence version) bounds `∫⁻ liminf ≤ liminf ∫⁻`.
  have h_fatou :
      ∫⁻ y, Filter.atTop.liminf (fun n => L (y - htil_seq n)) ∂ν
        ≤ Filter.atTop.liminf (fun n => ∫⁻ y, L (y - htil_seq n) ∂ν) :=
    MeasureTheory.lintegral_liminf_le (μ := ν)
      (fun n => hL_shift_meas (htil_seq n))
  -- Step 3: chain — `F htil ≤ ∫⁻ liminf ≤ liminf F (htil_seq n) ≤ c`.
  have h_F_le_integral_liminf :
      F htil ≤ ∫⁻ y, Filter.atTop.liminf (fun n => L (y - htil_seq n)) ∂ν := by
    refine MeasureTheory.lintegral_mono ?_
    intro y; exact h_pt y
  refine (h_F_le_integral_liminf.trans h_fatou).trans ?_
  -- `liminf F (htil_seq n) ≤ c` since `F (htil_seq n) ≤ c` eventually (actually always).
  refine Filter.liminf_le_of_le ?_ ?_
  · exact ⟨0, by simp⟩
  · intro b hb
    -- We need: there exists `n` with `F (htil_seq n) ≤ b`. From eventually `≤ c`, then `≤ b` if c ≤
    -- b.
    -- Actually `hb : ∀ᶠ n, b ≤ F (htil_seq n)`. We want `b ≤ c`.
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (h_mem n)

/-- **Rational sup-lift for lsc integrands on `EuclideanSpace`.**

vdV §8.5: the outer uncountable sup over finite subsets of `ℝ^k` in the
conclusion of Theorem 8.11 is reducible to a countable sup over finite subsets
of a rational dense subset, provided the inner integrand is lsc.

Standard density argument: each finite `I ⊂ ℝ^k` can be approximated by
a rational finite subset `I_ε ⊂ ℚ^k`, and lsc preserves the inequality
through the limit. -/
theorem iSup_finite_le_iSup_rational_finite_via_lsc
    {k : ℕ} (g : Θ k → ℝ≥0∞) (hg_lsc : LowerSemicontinuous g) :
    (⨆ I : Finset (Θ k), ⨆ h ∈ I, g h)
      ≤ ⨆ I : Finset {h : Θ k //
                ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))},
          ⨆ h ∈ I, g (h : Θ k) := by
  -- Step 1+2: collapse both nested Finset suprema to plain suprema via
  -- `iSup_eq_iSup_finset`.
  rw [show (⨆ I : Finset (Θ k), ⨆ h ∈ I, g h) = ⨆ h : Θ k, g h from
        (iSup_eq_iSup_finset (s := g)).symm,
      show (⨆ I : Finset {h : Θ k //
                ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))},
              ⨆ h ∈ I, g (h : Θ k)) =
            ⨆ h : {h : Θ k //
                ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))},
              g (h : Θ k) from
        (iSup_eq_iSup_finset
          (s := fun (h : {h : Θ k //
                ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))}) =>
            g (h : Θ k))).symm]
  -- Step 3+4: pointwise comparison.
  refine iSup_le (fun h₀ => ?_)
  -- Step 5: for each coordinate i, pick a rational sequence converging to the i-th
  -- coordinate of h₀ (via Rat.denseRange_cast + mem_closure_iff_seq_limit on ℝ,
  -- which is a metric space ⇒ FrechetUrysohn).
  have h_dense_R : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
  have h_coord : ∀ i : Fin k, ∃ q : ℕ → ℚ,
      Filter.Tendsto (fun n => ((q n : ℝ))) Filter.atTop
        (𝓝 ((WithLp.equiv 2 (Fin k → ℝ)) h₀ i)) := by
    intro i
    have h_mem : (WithLp.equiv 2 (Fin k → ℝ)) h₀ i ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by
      rw [h_dense_R.closure_range]; trivial
    rcases mem_closure_iff_seq_limit.mp h_mem with ⟨x, hx_mem, hx_tendsto⟩
    choose q hq using hx_mem
    refine ⟨q, ?_⟩
    have h_eq : (fun n => ((q n : ℝ))) = x := by funext n; exact hq n
    rw [h_eq]; exact hx_tendsto
  choose q_seq hq_seq using h_coord
  -- Define the candidate rational sequence in Θ k via WithLp.equiv.symm.
  set y : ℕ → Θ k :=
    fun n => (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => (q_seq i n : ℝ)) with hy_def
  -- y n → h₀ in Θ k: convergence in PiLp 2 ≃ₜ (Fin k → ℝ) reduces to pointwise.
  have hy_tendsto : Filter.Tendsto y Filter.atTop (𝓝 h₀) := by
    -- It suffices to show `(WithLp.equiv 2 _) ∘ y → (WithLp.equiv 2 _) h₀`
    -- in `Fin k → ℝ`, since `(WithLp.equiv 2 _).symm` is continuous.
    have h_inner : Filter.Tendsto
        (fun n => (fun i => (q_seq i n : ℝ))) Filter.atTop
        (𝓝 ((WithLp.equiv 2 (Fin k → ℝ)) h₀)) := by
      rw [tendsto_pi_nhds]
      intro i
      exact hq_seq i
    -- Apply continuity of the inverse `WithLp.equiv 2 _`.symm = toLp 2.
    have h_cont : Continuous (fun x : Fin k → ℝ =>
        (WithLp.equiv 2 (Fin k → ℝ)).symm x) :=
      PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)
    exact (h_cont.tendsto _).comp h_inner
  -- Step 6: by lsc, g h₀ ≤ liminf (g ∘ y) atTop.
  have h_lsc_liminf : g h₀ ≤ Filter.liminf (fun n => g (y n)) Filter.atTop := by
    have h_lsc : g h₀ ≤ Filter.liminf g (𝓝 h₀) := hg_lsc.le_liminf h₀
    have h_map : Filter.map y Filter.atTop ≤ 𝓝 h₀ := hy_tendsto
    have h_le : Filter.liminf g (𝓝 h₀) ≤ Filter.liminf g (Filter.map y Filter.atTop) :=
      Filter.liminf_le_liminf_of_le h_map
    -- Filter.liminf g (Filter.map y _) = Filter.liminf (g ∘ y) _.
    have h_eq : Filter.liminf g (Filter.map y Filter.atTop) =
        Filter.liminf (g ∘ y) Filter.atTop := (Filter.liminf_comp g y _).symm
    exact h_lsc.trans (h_le.trans h_eq.le)
  -- Step 7: liminf (g ∘ y) ≤ ⨆ n, g (y n).
  have h_liminf_le_iSup : Filter.liminf (fun n => g (y n)) Filter.atTop ≤
      ⨆ n : ℕ, g (y n) := by
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    refine iSup_le (fun n => ?_)
    -- ⨅ i, ⨅ (_ : i ≥ n), g (y i) ≤ g (y n) by instantiating i = n.
    have h1 : (⨅ i : ℕ, ⨅ (_ : i ≥ n), g (y i)) ≤ ⨅ (_ : n ≥ n), g (y n) :=
      iInf_le _ n
    have h2 : (⨅ (_ : n ≥ n), g (y n)) ≤ g (y n) := iInf_le _ (le_refl n)
    exact (h1.trans h2).trans (le_iSup (fun n => g (y n)) n)
  -- Step 8: ⨆ n, g (y n) ≤ ⨆ h : rational subtype, g (h : Θ k).
  have h_iSup_le : (⨆ n : ℕ, g (y n)) ≤
      ⨆ h : {h : Θ k //
              ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))},
        g (h : Θ k) := by
    refine iSup_le (fun n => ?_)
    -- Build the rational-subtype witness and apply le_iSup.
    refine le_iSup
      (fun (h : {h : Θ k //
        ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))}) =>
        g (h : Θ k))
      (⟨y n, fun i => q_seq i n, by simp [hy_def]⟩ :
        {h : Θ k //
          ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))})
  exact h_lsc_liminf.trans (h_liminf_le_iSup.trans h_iSup_le)

/-! ## Per-rational-`h` LHS bound via joint sub-sequence

The substantive measure-theoretic core of the LHS witness. Given the standard
vdV §8.11 setup, a Prokhorov subsequence `(φ, ψ_inner)` of the joint pushforward
and its joint weak limit `π`, the goal is, for each rational `h`, a bound
`LHS_h(representationKernel J π) ≤ liminf_φ (consumer integrand at h)`.

The chain is:

1. Per-rational-`h`, run the Le Cam 3 + Theorem 8.3 chain: joint subseq +
   log-likelihood Slutsky bridge ⇒ joint+log-lik weak conv ⇒ tilt formula ⇒
   `(P^n_h).map(√n(T-ψθ₀)) ⇝ (mvg h J⁻¹).bind κ`.
2. Slutsky-Fréchet shift: `√n(ψ(θ₀+h/√n) - ψθ₀) → ψDot h`, so
   `(P^n_h).map(√n(T - ψ(θ₀+h/√n))) ⇝ ((mvg h J⁻¹).bind κ).map(· - ψDot h)`.
3. Portmanteau-lsc bridge + change-of-vars:
   `LHS_h(κ) ≤ liminf-along-(φ ∘ ψ_inner ∘ ρ) of (consumer-at-h-integral)`.

This is decomposed into the named bricks below:

* `le_cam_3_per_rational_h_weak_conv`: `slutsky_bridge_of_lanResidual` +
  `joint_weak_with_logLikelihood` + `limit_law_under_h` give per-rational-h
  weak convergence of `(P^{n_k}_h).map(√{n_k}·(T - ψ θ₀))` to the tilted marginal.
* `representation_kernel_identifies_le_cam_3_limit`: the tilted marginal equals
  `(multivariateGaussian h J⁻¹).bind κ` where `κ := representationKernel J π`,
  via `gaussianShift_bind_eq_limit` + score-CLT-marginal identification.
* `slutsky_frechet_shift_translation_per_h`: Slutsky on the Fréchet shift
  `√{n_k}·(ψ(θ₀+h/√{n_k}) - ψ θ₀) → ψDot h`, shifting the weak conv from
  "centered at ψ θ₀" to "centered at ψ(θ₀+h/√{n_k})", with limit
  `((mvg h J⁻¹).bind κ).map(· - ψDot h)`.
* `portmanteau_lsc_assembly_per_h`: Portmanteau-lsc bridge + change-of-vars.

A sub-sub-sub-sequence of `φ` cannot attain the original `φ`-liminf in general
(a subsequence's liminf is ≥ the original's, with no construction forcing
equality at arbitrary `h`). The parent therefore bounds `LHS_h ≤
liminf-along-(φ ∘ ψ_inner ∘ ρ_h)-at-h` (the subsequence's own liminf,
attainable via cluster-point extraction), and the downstream
`diagonal_subseq_kernel_lift` bridges to `localAsymptoticRisk` via the
sup-over-Finset structure. -/

/-- **Per-rational-h Le Cam 3 + Theorem 8.3 weak convergence to the
tilted marginal.** Inner brick of `lhs_bound_for_rational_h_via_joint_subseq`.

Mirrors Steps 3–5 of `LAN_representation`'s body, specialised to a single
rational `h`:

1. `slutsky_bridge_of_lanResidual` discharges the Slutsky perturbation
   hypothesis from `lanResidual_tendsto_productMeasure`.
2. `joint_weak_with_logLikelihood` produces the joint weak limit
   `(T, logLikelihood) ⇝ π.map(p ↦ (p.1, ⟪h, p.2⟫ - ½⟨h, Jh⟩))`.
3. `limit_law_under_h` extracts the tilted-marginal form of the limit
   measure under `P^n_h`.

Conclusion: along `(φ ∘ ψ_inner ∘ ρ)`, the pushforward
`(P^{n_k}_h).map(√{n_k}·(T - ψ θ₀))` weakly converges to
`Measure.map Prod.fst (π.withDensity (exp ∘ tilt-by-h))`, which
`representation_kernel_identifies_le_cam_3_limit` identifies as
`(multivariateGaussian h J⁻¹).bind (representationKernel J π)`.

**Note on instance constraints**: requires `[HasOuterApproxClosed (𝓨 d)]`
and `[BorelSpace (𝓨 d)]` (inherited from EuclideanSpace abbreviation +
Mathlib's auto-instances). -/
theorem le_cam_3_per_rational_h_weak_conv
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (_hφ_mono : StrictMono φ)
    (ψ_inner : ℕ → ℕ) (_hψ_inner_mono : StrictMono ψ_inner)
    (ρ : ℕ → ℕ) (_hρ_mono : StrictMono ρ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (_hπ_conv_subsubseq : WeakConverges
      (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀
                        (φ (ψ_inner (ρ k_idx)))).map
        (fun ω => ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                    (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀),
                   AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner (ρ k_idx))) ω))) π)
    (h : Θ k)
    (_h_rat : ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) :
    WeakConverges
      (fun k_idx : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
            (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => (Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
            (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀)))
      (Measure.map Prod.fst
        (π.withDensity (fun p => ENNReal.ofReal
          (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm
                  (J.mulVec ((WithLp.equiv 2 _) h))⟫))))) := by
  -- Abbreviate the composed subsequence `n_k = φ (ψ_inner (ρ k))`.
  set φ_full : ℕ → ℕ := fun k => φ (ψ_inner (ρ k)) with hφ_full_def
  -- The rescaled-shifted statistic `T' n ω := √n • (T n ω - ψ θ₀)`.
  let T' : ∀ n, (Fin n → 𝓧) → 𝓨 d :=
    fun n ω => (Real.sqrt n) • (T n ω - ψ θ₀)
  have hT'_meas : ∀ n, Measurable (T' n) := fun n =>
    ((hT_meas n).sub measurable_const).const_smul (Real.sqrt n)
  -- Derive product-measure probability instances internally from `hPDF`.
  haveI : ∀ θ : Θ k, ∀ n, IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Unpack `hPDF`.
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  -- Step 1: Score CLT (`Δ_n ⇝ N(0, J)` under `P^n_{θ₀}`).
  have hScoreCLT : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
        (AsymptoticRepresentation.scoreSum ℓ n))
      (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) :=
    AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint h_one_perturb
      hint_perturb hDQM J hJ.posSemidef hJ_fisher
  -- Step 2: vLog + hLogLik_weak (asymptotic log-normality of the log-likelihood
  -- under `P^n_{θ₀}`). The LAN/Le Cam transfer routes through the DQM-derived
  -- asymptotic integral comparison.
  let vLog : NNReal := (h.ofLp ⬝ᵥ J.mulVec h.ofLp).toNNReal
  have h_vLog_coe : (vLog : ℝ) = h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
    have h_nn : 0 ≤ h.ofLp ⬝ᵥ J.mulVec h.ofLp := by
      have := hJ.posSemidef.re_dotProduct_nonneg (x := (h.ofLp : Fin k → ℝ))
      simpa using this
    exact Real.coe_toNNReal _ h_nn
  have h_vLog_eq_fisher :
      (vLog : ℝ)
        = ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
    rw [h_vLog_coe]
    change _ = inner ℝ h ((Matrix.toEuclideanCLM (𝕜 := ℝ) J) h)
    rw [Matrix.inner_toEuclideanCLM]
  have hΔ_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := by
    intro n
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have hLogLik_weak :
      WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.logLikelihood M θ₀ h n))
        (ProbabilityTheory.gaussianReal (-(vLog : ℝ) / 2) vLog) := by
    have h_inner_cont : Continuous (fun v : Θ k => ⟪h, v⟫) :=
      continuous_const.inner continuous_id
    have h_inner_meas : Measurable (fun v : Θ k => ⟪h, v⟫) :=
      h_inner_cont.measurable
    -- Step A: `⟨h, Δ_n⟩ ⇝ gaussianReal 0 (vLog h)`.
    have h_compA : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (AsymptoticRepresentation.scoreSum ℓ n)).map
            (fun v : Θ k => ⟪h, v⟫)) := by
      funext n
      exact (Measure.map_map h_inner_meas (hΔ_meas n)).symm
    have h_scalarCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫))
        (ProbabilityTheory.gaussianReal 0 vLog) := by
      rw [h_compA]
      have h_map := hScoreCLT.map h_inner_cont h_inner_meas
      rwa [ProbabilityTheory.multivariateGaussian_map_inner_eq_gaussianReal h
        hJ.posSemidef] at h_map
    -- Step B: shift by `-(vLog/2)`.
    have h_sub_cont : Continuous (fun y : ℝ => y - (vLog : ℝ) / 2) := by fun_prop
    have h_sub_meas : Measurable (fun y : ℝ => y - (vLog : ℝ) / 2) :=
      h_sub_cont.measurable
    have h_compB : (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog : ℝ) / 2))
        = (fun n => ((AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫)).map
              (fun y : ℝ => y - (vLog : ℝ) / 2)) := by
      funext n
      exact (Measure.map_map h_sub_meas
        (h_inner_meas.comp (hΔ_meas n))).symm
    have h_shiftedCLT : WeakConverges
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (fun ω => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog : ℝ) / 2))
        (ProbabilityTheory.gaussianReal (-(vLog : ℝ) / 2) vLog) := by
      rw [h_compB]
      have h_map := h_scalarCLT.map h_sub_cont h_sub_meas
      rw [ProbabilityTheory.gaussianReal_map_sub_const ((vLog : ℝ) / 2),
        zero_sub, ← neg_div] at h_map
      exact h_map
    -- Step C: Slutsky with the LAN residual.
    have h_resid := AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ_fisher h
    have hc_as_fisher :
        (vLog : ℝ) / 2 = (1/2 : ℝ) *
          ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ := by
      rw [← h_vLog_eq_fisher]; ring
    have hX_ae : ∀ n, AEMeasurable
        (fun ω : Fin n → 𝓧 => ⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog : ℝ) / 2)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      ((h_inner_meas.comp (hΔ_meas n)).sub_const _).aemeasurable
    have hY_ae : ∀ n, AEMeasurable (AsymptoticRepresentation.logLikelihood M θ₀ h n)
        (AsymptoticRepresentation.productMeasure M μ θ₀ n) := fun n =>
      (AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n).aemeasurable
    have h_dist_tendsto : ∀ ε > 0, Tendsto
        (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).real
          {ω : Fin n → 𝓧 | ε ≤ dist
              (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h n ω)})
        atTop (𝓝 0) := by
      intro ε hε
      have h_set_eq : ∀ n,
          {ω : Fin n → 𝓧 | ε ≤ dist
              (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (vLog : ℝ) / 2)
              (AsymptoticRepresentation.logLikelihood M θ₀ h n ω)}
            = {ω | ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h n ω
                - (⟪h, AsymptoticRepresentation.scoreSum ℓ n ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm
                      (J.mulVec ((WithLp.equiv 2 _) h))⟫)|} := by
        intro n
        ext ω
        simp only [Set.mem_setOf_eq, Real.dist_eq, hc_as_fisher]
        rw [abs_sub_comm]
      simp_rw [h_set_eq]
      exact h_resid ε hε
    exact WeakConverges.slutsky_of_tendstoInMeasure_dist
      hX_ae hY_ae h_shiftedCLT h_dist_tendsto
  -- Step 3: Slutsky bridge along `φ_full` to upgrade the linearised joint
  -- (using `_hπ_conv_subsubseq`) to the log-likelihood joint.
  have hφ_full_mono : StrictMono φ_full :=
    _hφ_mono.comp (_hψ_inner_mono.comp _hρ_mono)
  have h_lanResidual_full :=
    AsymptoticRepresentation.lanResidual_tendsto_productMeasure M μ θ₀ ℓ hℓ
      h_one hint h_one_perturb hint_perturb hDQM J hJ_fisher h
  have h_lanResidual_subseq : ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full k_idx)).real
        {ω : Fin (φ_full k_idx) → 𝓧 |
          ε ≤ |AsymptoticRepresentation.logLikelihood M θ₀ h (φ_full k_idx) ω
                 - (⟪h, AsymptoticRepresentation.scoreSum ℓ (φ_full k_idx) ω⟫ - (1/2 : ℝ) *
                    ⟪h, (WithLp.equiv 2 _).symm
                      (J.mulVec ((WithLp.equiv 2 _) h))⟫)|})
        atTop (𝓝 0) := fun ε hε =>
    (h_lanResidual_full ε hε).comp hφ_full_mono.tendsto_atTop
  have hSlutsky_π := AsymptoticRepresentation.slutsky_bridge_of_lanResidual M μ θ₀ ℓ hℓ J T'
    hT'_meas h π φ_full
    (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)
    h_lanResidual_subseq
  -- Step 4: joint weak convergence with log-likelihood along `φ_full`.
  have h_joint_log := AsymptoticRepresentation.joint_weak_with_logLikelihood
    M μ θ₀ ℓ hℓ hDQM J hJ_fisher T' hT'_meas h π φ_full hφ_full_mono
    _hπ_conv_subsubseq hSlutsky_π
  -- Step 5: apply Le Cam's third lemma along `φ_full`. Discharges Step 5's
  -- two integrability hypotheses via `integrable_exp_tilt` /
  -- `integral_exp_tilt_eq_one` (needs `π.map snd = N(0, J)`).
  -- First, identify `π.map snd = multivariateGaussian 0 J` using `_hπ_conv_subsubseq`
  -- + `hScoreCLT` + weak-limit uniqueness.
  have h_π_snd : π.map Prod.snd =
      ProbabilityTheory.multivariateGaussian (0 : Θ k) J := by
    have h_marg : ∀ k_idx,
        ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full k_idx)).map
            (fun ω => ((Real.sqrt (φ_full k_idx)) •
                        (T (φ_full k_idx) ω - ψ θ₀),
                       AsymptoticRepresentation.scoreSum ℓ (φ_full k_idx) ω))).map Prod.snd
          = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full k_idx)).map
            (AsymptoticRepresentation.scoreSum ℓ (φ_full k_idx)) := by
      intro k_idx
      rw [Measure.map_map measurable_snd
        ((hT'_meas (φ_full k_idx)).prodMk (hΔ_meas (φ_full k_idx)))]
      rfl
    have hν : WeakConverges
        (fun k_idx => ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full k_idx)).map
          (fun ω => ((Real.sqrt (φ_full k_idx)) •
                      (T (φ_full k_idx) ω - ψ θ₀),
                     AsymptoticRepresentation.scoreSum ℓ (φ_full k_idx) ω))).map Prod.snd)
        (ProbabilityTheory.multivariateGaussian (0 : Θ k) J) := by
      simp_rw [h_marg]
      exact hScoreCLT.comp hφ_full_mono
    exact WeakConverges.snd_eq _hπ_conv_subsubseq hν
  -- Discharge the MGF integrability pair using the marginal identification.
  have h_mgfTilt_integrable := ProbabilityTheory.integrable_exp_tilt
    π J hJ.posSemidef h_π_snd h
  have h_mgfTilt_integral_one := ProbabilityTheory.integral_exp_tilt_eq_one
    π J hJ.posSemidef h_π_snd h
  -- DQM-derived asymptotic singular-mass control, derived internally from `hDQM`
  -- + `hPDF`. These do not depend on the statistic, only on the log-likelihood;
  -- supply the perturbation direction `h`.
  have h_exp_int_full :=
    AsymptoticRepresentation.productMeasure_exp_logLikelihood_integrable M μ θ₀ ℓ hℓ hDQM hPDF h
  have h_mass_full :=
    AsymptoticRepresentation.productMeasure_integral_exp_logLikelihood_tendsto_one M μ θ₀ ℓ hℓ hDQM
        hPDF h
  -- Uniform integrability of `exp(L_n)` along `φ_full`, via the contiguity-footing
  -- variant + subsequence specialisation (`StrictMono.id_le`).
  have h_UI_full := Contiguity.uniform_integrability_exp_L_of_integral_tendsto_one
    (Ω := fun n => Fin n → 𝓧)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ n)
    (fun n => AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n)
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h n)
    (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h n)
    h_exp_int_full h_mass_full vLog hLogLik_weak
  have h_UI_subseq : ∀ ε : ℝ, 0 < ε →
      ∃ Mbd : ℝ, 0 ≤ Mbd ∧ ∃ N₀ : ℕ, ∀ n, N₀ ≤ n →
        ∫ ω, Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ_full n) ω) -
            min (Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ_full n) ω)) Mbd
          ∂(AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full n)) ≤ ε := by
    intro ε hε
    obtain ⟨Mbd, hMbd, N₀, hN₀⟩ := h_UI_full ε hε
    refine ⟨Mbd, hMbd, N₀, fun n hn => hN₀ (φ_full n)
      (le_trans hn (hφ_full_mono.id_le n))⟩
  -- Define the tilt-map sending `π` to its `(fst, ⟨h, snd⟩ - 1/2 ⟨h, Jh⟩)` tilt.
  let g : Θ k → ℝ := fun δ =>
    ⟪h, δ⟫ - (1 / 2 : ℝ) *
      ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫
  let tilt_map : 𝓨 d × Θ k → 𝓨 d × ℝ := fun p => (p.1, g p.2)
  have hg_meas : Measurable g :=
    (continuous_const.inner continuous_id).measurable.sub measurable_const
  have htilt_meas : Measurable tilt_map :=
    measurable_fst.prodMk (hg_meas.comp measurable_snd)
  haveI h_tilt_prob : IsProbabilityMeasure (π.map tilt_map) :=
    MeasureTheory.Measure.isProbabilityMeasure_map htilt_meas.aemeasurable
  -- Main integral-comparison bound (full sequence) for the rescaled-shifted statistic
  -- `T'` (the bound is statistic-agnostic), then specialise to `φ_full`.
  obtain ⟨ρ_cmp, hρ_cmp_tendsto, hρ_cmp_bound⟩ :=
    AsymptoticRepresentation.productMeasure_integral_comparison M μ θ₀ ℓ hℓ hDQM hPDF T' hT'_meas h
  have h_int_cmp_subseq :
      ∃ ρ' : ℕ → ℝ, Filter.Tendsto ρ' Filter.atTop (𝓝 0) ∧
        ∀ (f : BoundedContinuousFunction (𝓨 d) ℝ) (n : ℕ),
          |∫ ω, f (T' (φ_full n) ω)
              ∂(AsymptoticRepresentation.productMeasure M μ
                  (θ₀ + (Real.sqrt (φ_full n))⁻¹ • h) (φ_full n))
            - ∫ ω, f (T' (φ_full n) ω)
                * Real.exp (AsymptoticRepresentation.logLikelihood M θ₀ h (φ_full n) ω)
                ∂(AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full n))| ≤ ‖f‖ * ρ' n :=
    ⟨ρ_cmp ∘ φ_full, hρ_cmp_tendsto.comp hφ_full_mono.tendsto_atTop,
      fun f n => hρ_cmp_bound f (φ_full n)⟩
  -- Apply Le Cam's third lemma (contiguity-footing variant) along `φ_full`. The
  -- `joint_weak` input is exactly `h_joint_log`, which has limit `π.map tilt_map`.
  have h_lecam := Contiguity.weak_limit_under_Q_of_lecam_third_of_integral_comparison
    (Ω := fun n => Fin (φ_full n) → 𝓧) (E := 𝓨 d)
    (fun n => AsymptoticRepresentation.productMeasure M μ θ₀ (φ_full n))
    (fun n => AsymptoticRepresentation.productMeasure M μ
                  (θ₀ + (Real.sqrt (φ_full n))⁻¹ • h) (φ_full n))
    (fun n => T' (φ_full n))
    (fun n => AsymptoticRepresentation.logLikelihood M θ₀ h (φ_full n))
    (fun n => hT'_meas (φ_full n))
    (fun n => AsymptoticRepresentation.logLikelihood_measurable M θ₀ h (φ_full n))
    h_int_cmp_subseq
    (π.map tilt_map) h_joint_log
    h_UI_subseq h_mgfTilt_integrable h_mgfTilt_integral_one
  -- `h_lecam` gives weak conv to `((π.map tilt_map).withDensity (exp ∘ snd)).map fst`.
  -- Reconcile this with the target form via `Measure.withDensity_map_eq_map_withDensity`
  -- + `Measure.map_map`.
  have h_target_eq :
      ((π.map tilt_map).withDensity
          (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2))).map Prod.fst
        = Measure.map Prod.fst
          (π.withDensity (fun p => ENNReal.ofReal
            (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
              ⟪h, (WithLp.equiv 2 _).symm
                    (J.mulVec ((WithLp.equiv 2 _) h))⟫)))) := by
    have h_exp_snd_meas :
        Measurable (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) :=
      (Real.continuous_exp.measurable.comp measurable_snd).ennreal_ofReal
    rw [Measure.withDensity_map_eq_map_withDensity π _ htilt_meas
      (fun q : 𝓨 d × ℝ => ENNReal.ofReal (Real.exp q.2)) h_exp_snd_meas]
    rw [MeasureTheory.Measure.map_map measurable_fst htilt_meas]
    rfl
  rw [← h_target_eq]
  exact h_lecam

/-- **Representation-kernel identification of the Le Cam 3 limit.**
Inner brick of `lhs_bound_for_rational_h_via_joint_subseq`.

The tilted-marginal `Measure.map Prod.fst (π.withDensity (exp ∘ tilt-by-h))`
emerging from `limit_law_under_h` (the conclusion of
`le_cam_3_per_rational_h_weak_conv`) equals the Gaussian-shift bind
`(multivariateGaussian h J⁻¹).bind (representationKernel J π)`.

**Mathematical content**: this is the content of `gaussianShift_bind_eq_limit`
applied with `gauss := multivariateGaussian · J⁻¹` (which `IsGaussianShift`
witnesses), `L_h := <tilted marginal>` (auto-probability via the MGF
identity `integral_exp_tilt_eq_one`). Requires identifying
`π.map Prod.snd = multivariateGaussian 0 J` (score CLT + `WeakConverges.snd_eq`
applied to the inherited joint weak conv along `φ ∘ ψ_inner ∘ ρ`). -/
theorem representation_kernel_identifies_le_cam_3_limit
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (_hφ_mono : StrictMono φ)
    (ψ_inner : ℕ → ℕ) (_hψ_inner_mono : StrictMono ψ_inner)
    (ρ : ℕ → ℕ) (_hρ_mono : StrictMono ρ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (_hπ_conv_subsubseq : WeakConverges
      (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀
                        (φ (ψ_inner (ρ k_idx)))).map
        (fun ω => ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                    (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀),
                   AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner (ρ k_idx))) ω))) π)
    (h : Θ k)
    (_h_rat : ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) :
    Measure.map Prod.fst
        (π.withDensity (fun p => ENNReal.ofReal
          (Real.exp (⟪h, p.2⟫ - (1 / 2 : ℝ) *
            ⟪h, (WithLp.equiv 2 _).symm
                  (J.mulVec ((WithLp.equiv 2 _) h))⟫))))
      = (multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π) := by
  classical
  -- Standard-Borel / Nonempty instances for the target space (from PolishSpace).
  haveI : StandardBorelSpace (𝓨 d) := inferInstance
  haveI : Nonempty (𝓨 d) := ⟨(0 : 𝓨 d)⟩
  -- IsProbabilityMeasure on each productMeasure from the PDF hypothesis.
  haveI hProd_prob : ∀ θ : Θ k, ∀ n, IsProbabilityMeasure
      (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Subseq composition `n_k := φ (ψ_inner (ρ k))` is strictly monotone.
  have hχ_mono : StrictMono (fun k_idx => φ (ψ_inner (ρ k_idx))) :=
    _hφ_mono.comp (_hψ_inner_mono.comp _hρ_mono)
  -- Score CLT + Prohorov: `(P^n_{θ₀}).map (scoreSum ℓ n) ⇝ multivariateGaussian 0 J`.
  have hJ_psd : J.PosSemidef := hJ.posSemidef
  have h_one : ∫ x, M.density θ₀ x ∂μ = 1 := hPDF.density_integral_eq_one θ₀
  have hint : Integrable (M.density θ₀) μ := hPDF.density_integrable θ₀
  have h_one_perturb : ∀ t : ℝ, ∀ u : Θ k,
      ∫ x, M.density (θ₀ + t • u) x ∂μ = 1 :=
    fun t u => hPDF.density_integral_eq_one (θ₀ + t • u)
  have hint_perturb : ∀ t : ℝ, ∀ u : Θ k,
      Integrable (M.density (θ₀ + t • u)) μ :=
    fun t u => hPDF.density_integrable (θ₀ + t • u)
  have hScoreCLT : WeakConverges
      (fun n => (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
          (AsymptoticRepresentation.scoreSum ℓ n))
      (multivariateGaussian (0 : Θ k) J) :=
    AsymptoticRepresentation.scoreSum_weakly_converges M μ θ₀ ℓ hℓ h_one hint
      h_one_perturb hint_perturb hDQM J hJ_psd hJ_fisher
  -- Measurabilities for the joint pushforward (needed to identify the snd-marginal).
  have h_T_n_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      (Real.sqrt n) • (T n ω - ψ θ₀)) := fun n =>
    ((hT_meas n).sub_const _).const_smul (Real.sqrt n)
  have h_score_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := fun n => by
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_pair_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      ((Real.sqrt n) • (T n ω - ψ θ₀), AsymptoticRepresentation.scoreSum ℓ n ω)) :=
    fun n => (h_T_n_meas n).prodMk (h_score_meas n)
  -- The snd-marginal of each joint pushforward equals the scoreSum pushforward.
  have h_marg : ∀ k_idx,
      ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                      (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀),
                     AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner (ρ k_idx))) ω))).map Prod.snd
        = (AsymptoticRepresentation.productMeasure M μ θ₀ (φ (ψ_inner (ρ k_idx)))).map
            (AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner (ρ k_idx)))) := by
    intro k_idx
    rw [Measure.map_map measurable_snd (h_pair_meas (φ (ψ_inner (ρ k_idx))))]
    rfl
  -- Score CLT pulled along `n_k = φ ∘ ψ_inner ∘ ρ`.
  have hScoreCLT_subseq : WeakConverges
      (fun k_idx => ((AsymptoticRepresentation.productMeasure M μ θ₀ (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                      (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀),
                     AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner (ρ k_idx))) ω))).map Prod.snd)
      (multivariateGaussian (0 : Θ k) J) := by
    simp_rw [h_marg]
    exact hScoreCLT.comp hχ_mono
  -- Identify `π.map Prod.snd = multivariateGaussian 0 J` via WeakConverges.snd_eq.
  have h_π_snd : π.map Prod.snd = multivariateGaussian (0 : Θ k) J :=
    WeakConverges.snd_eq _hπ_conv_subsubseq hScoreCLT_subseq
  -- The abstract Gaussian-shift family `gauss h := multivariateGaussian h J⁻¹`.
  set gauss : Θ k → Measure (Θ k) := fun h => multivariateGaussian h J⁻¹ with hgauss
  have hGauss : GaussianShift.IsGaussianShift gauss J⁻¹ :=
    GaussianShift.isGaussianShift_multivariateGaussian J⁻¹ hJ.inv
  -- Discharge the `HasTiltedLinearPushforward` provider at `π.map Prod.snd`.
  have hTilt_π : GaussianShift.HasTiltedLinearPushforward gauss (π.map Prod.snd) J := by
    rw [h_π_snd]
    exact GaussianShift.hasTiltedLinearPushforward_of_isGaussianShift hJ hGauss
  -- IsProbabilityMeasure of the target tilted-marginal measure, via the MGF identity.
  -- Strategy: `(π.withDensity f) Set.univ = ∫⁻ p, f p ∂π = ENNReal.ofReal (∫ p, exp ... ∂π)
  -- = ENNReal.ofReal 1 = 1`. The Bochner side uses `integral_exp_tilt_eq_one` after
  -- transport along `tilt_map`.
  set c : ℝ := (1 / 2 : ℝ) *
      ⟪h, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) h))⟫ with hc_def
  set tilt_map : 𝓨 d × Θ k → 𝓨 d × ℝ :=
    fun p => (p.1, ⟪h, p.2⟫ - c) with htilt_map
  have htilt_meas : Measurable tilt_map :=
    measurable_fst.prodMk
      (((continuous_const.inner continuous_id).measurable.comp measurable_snd).sub_const _)
  -- Bochner-integral form of the tilted density, via change of variables to π.map tilt_map.
  have h_int_one : ∫ p, Real.exp (⟪h, p.2⟫ - c) ∂π = 1 := by
    have h_eq : ∫ p, Real.exp (⟪h, p.2⟫ - c) ∂π
        = ∫ q : 𝓨 d × ℝ, Real.exp q.2 ∂(π.map tilt_map) := by
      rw [integral_map htilt_meas.aemeasurable (by fun_prop)]
    rw [h_eq]
    exact ProbabilityTheory.integral_exp_tilt_eq_one π J hJ_psd h_π_snd h
  have h_int_integrable : Integrable (fun p : 𝓨 d × Θ k =>
      Real.exp (⟪h, p.2⟫ - c)) π := by
    have h_src := ProbabilityTheory.integrable_exp_tilt π J hJ_psd h_π_snd h
    -- `h_src : Integrable (fun q => exp q.2) (π.map tilt_map)`.
    have h_strong : AEStronglyMeasurable
        (fun q : 𝓨 d × ℝ => Real.exp q.2) (π.map tilt_map) := by fun_prop
    exact (integrable_map_measure h_strong htilt_meas.aemeasurable).mp h_src
  -- Lift Bochner integral = 1 to lintegral ofReal = 1 (since exp ≥ 0).
  have h_lint_one : ∫⁻ p, ENNReal.ofReal (Real.exp (⟪h, p.2⟫ - c)) ∂π = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_int_integrable
        (Filter.Eventually.of_forall (fun _ => (Real.exp_pos _).le)),
      h_int_one, ENNReal.ofReal_one]
  haveI hWD_prob : IsProbabilityMeasure (π.withDensity (fun p => ENNReal.ofReal
      (Real.exp (⟪h, p.2⟫ - c)))) := by
    refine ⟨?_⟩
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact h_lint_one
  haveI hL_h_prob : IsProbabilityMeasure
      (Measure.map Prod.fst (π.withDensity (fun p => ENNReal.ofReal
        (Real.exp (⟪h, p.2⟫ - c))))) :=
    MeasureTheory.Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  -- Apply the closed brick `gaussianShift_bind_eq_limit` with `L_h := target` and
  -- `_hL_h_formula := rfl`. Conclusion is the target equality.
  exact AsymptoticRepresentation.gaussianShift_bind_eq_limit J hJ gauss hGauss π h
    (Measure.map Prod.fst (π.withDensity (fun p => ENNReal.ofReal
      (Real.exp (⟪h, p.2⟫ - c))))) hTilt_π rfl

/-- **Slutsky-Fréchet shift translating the weak limit by `· - ψDot h`.**
Inner brick of `lhs_bound_for_rational_h_via_joint_subseq`.

Given the weak conv with limit `tilted_marginal` and its identification
as `(mvg h J⁻¹).bind κ`, translate the weak convergence from
"`(P^{n_k}_h).map(√{n_k}·(T - ψ θ₀))`" to "`(P^{n_k}_h).map(√{n_k}·(T -
ψ(θ₀+h/√{n_k})))`" by Slutsky with the Fréchet-differentiability shift
`√{n_k}·(ψ(θ₀+h/√{n_k}) - ψ θ₀) → ψDot h`.

**Mathematical content**: `hψ_diff` + `HasFDerivAt.tendsto_sqrt_mul`
(or equivalent) gives the Fréchet shift in probability;
`WeakConverges.slutsky_of_tendstoInMeasure_dist` translates the weak limit
accordingly. The resulting limit is
`((mvg h J⁻¹).bind κ).map(fun y => y - ψDot h)`. -/
theorem slutsky_frechet_shift_translation_per_h
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (_ℓ : 𝓧 → Θ k)
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ : J.PosDef)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (_hφ_mono : StrictMono φ)
    (ψ_inner : ℕ → ℕ) (_hψ_inner_mono : StrictMono ψ_inner)
    (ρ : ℕ → ℕ) (_hρ_mono : StrictMono ρ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (h : Θ k)
    (_h_rat : ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ)))
    -- Input: the unshifted weak convergence.
    (_h_wc_unshifted : WeakConverges
      (fun k_idx : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
            (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => (Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
            (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀)))
      ((multivariateGaussian h J⁻¹).bind
        (AsymptoticRepresentation.representationKernel J π))) :
    WeakConverges
      (fun k_idx : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
            (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => (Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
            (T (φ (ψ_inner (ρ k_idx))) ω
              - ψ (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h))))
      (((multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π)).map
        (fun y : 𝓨 d => y - ψDot h)) := by
  -- Delegate to the public `ForMathlib` brick
  -- `WeakConverges.slutsky_shift_of_tendsto`, instantiated with the per-`k_idx`
  -- product measures and statistics `T (φ (ψ_inner (ρ k_idx)))`.
  set n_idx : ℕ → ℕ := fun k_idx => φ (ψ_inner (ρ k_idx)) with hn_idx_def
  have h_n_atTop : Tendsto n_idx atTop atTop :=
    ((_hφ_mono.tendsto_atTop.comp _hψ_inner_mono.tendsto_atTop).comp
      _hρ_mono.tendsto_atTop)
  haveI hPn_prob : ∀ k_idx,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ
        (θ₀ + (Real.sqrt (n_idx k_idx))⁻¹ • h) (n_idx k_idx)) := fun k_idx =>
    AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF _ _
  -- The deterministic null sequence `√(n_idx k_idx) • (ψ(θ₀+·) - ψθ₀) - ψDot h
  -- → 0`, obtained from the per-direction shift hypothesis composed along the
  -- subsequence `n_idx → ∞` and recentred by subtracting the constant `ψDot h`.
  have h_frechet_shift : Tendsto (fun k_idx : ℕ =>
        (Real.sqrt (n_idx k_idx)) •
            (ψ (θ₀ + (Real.sqrt (n_idx k_idx))⁻¹ • h) - ψ θ₀) - ψDot h)
      atTop (𝓝 0) := by
    have h_comp := (hψ_shift h).comp h_n_atTop
    have := h_comp.sub_const (ψDot h)
    simpa [Function.comp, sub_self] using this
  exact WeakConverges.slutsky_shift_of_tendsto
    (P := fun k_idx => AsymptoticRepresentation.productMeasure M μ
      (θ₀ + (Real.sqrt (n_idx k_idx))⁻¹ • h) (n_idx k_idx))
    (T := fun k_idx => T (n_idx k_idx))
    (fun k_idx => hT_meas (n_idx k_idx)) h_frechet_shift _h_wc_unshifted

/-- **Portmanteau-lsc bridge + change-of-vars + liminf attainer assembly.**
Inner brick of `lhs_bound_for_rational_h_via_joint_subseq`; closes the parent's
per-rational-h conclusion.

Given the shifted weak convergence (consumer-side rescaling at `h`'s
LAN-perturbation), apply the ENNReal-valued lsc Portmanteau bridge
(`lintegral_le_liminf_lintegral_of_lsc_ennreal_*`) on integrand `L` with
change-of-vars `y ↦ y - ψDot h`:

* `∫⁻ y, L (y - ψDot h) d((mvg h J⁻¹).bind κ)` = `∫⁻ z, L z d(((mvg h J⁻¹).bind κ).map (· - ψDot
h))`
  by `lintegral_map`.
* Portmanteau-lsc applied to the shifted weak conv and `L` gives this RHS
  bounded above by `Filter.liminf` (along `φ ∘ ψ_inner ∘ ρ`) of the
  consumer integrand at `h`.
* The liminf attainer gives the liminf along `φ ∘ ψ_inner ∘ ρ` equal to
  `Filter.liminf` along `φ` (`Tendsto.liminf_eq`).

Hence the parent's `LHS_h(κ) ≤ liminf-along-φ-at-h` follows. -/
theorem portmanteau_lsc_assembly_per_h
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k)
    (J : Matrix (Fin k) (Fin k) ℝ) (_hJ : J.PosDef)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (_hφ_mono : StrictMono φ)
    (ψ_inner : ℕ → ℕ) (_hψ_inner_mono : StrictMono ψ_inner)
    (ρ : ℕ → ℕ) (_hρ_mono : StrictMono ρ)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (h : Θ k)
    (_h_rat : ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ)))
    -- Input: the shifted weak convergence.
    (_h_wc_shifted : WeakConverges
      (fun k_idx : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
            (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => (Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
            (T (φ (ψ_inner (ρ k_idx))) ω
              - ψ (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h))))
      (((multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π)).map
        (fun y : 𝓨 d => y - ψDot h)))
    -- Input: the per-rational-h Tendsto attainer for this `h`.
    (_h_attain : Filter.Tendsto
      (fun k_idx : ℕ =>
        ∫⁻ ω,
            L ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                  (T (φ (ψ_inner (ρ k_idx))) ω
                    - ψ (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)))
          ∂(AsymptoticRepresentation.productMeasure M μ
              (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
              (φ (ψ_inner (ρ k_idx)))))
      Filter.atTop
      (𝓝 (Filter.liminf
        (fun k_idx : ℕ =>
          ∫⁻ ω,
              L ((Real.sqrt (φ k_idx)) •
                    (T (φ k_idx) ω - ψ (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h)))
            ∂(AsymptoticRepresentation.productMeasure M μ
                (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h) (φ k_idx)))
        Filter.atTop))) :
    ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
        (AsymptoticRepresentation.representationKernel J π))
      ≤ Filter.liminf
          (fun k_idx : ℕ =>
            ∫⁻ ω,
                L ((Real.sqrt (φ k_idx)) •
                      (T (φ k_idx) ω - ψ (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h)))
              ∂(AsymptoticRepresentation.productMeasure M μ
                  (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h) (φ k_idx)))
          Filter.atTop := by
  -- Abbreviations to keep terms tractable.
  set n_k : ℕ → ℕ := fun k_idx => φ (ψ_inner (ρ k_idx)) with hn_k_def
  set θ_k : ℕ → Θ k := fun k_idx => θ₀ + (Real.sqrt (n_k k_idx))⁻¹ • h with hθ_k_def
  -- Note: `g_k` cannot be `set` due to dependent `Fin (n_k k_idx) → 𝓧`. Inline it.
  set μs : ℕ → Measure (𝓨 d) :=
    fun k_idx => (AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx)).map
      (fun ω => (Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
    with hμs_def
  set targetShift : Measure (𝓨 d) :=
      ((multivariateGaussian h J⁻¹).bind (AsymptoticRepresentation.representationKernel J π)).map
        (fun y : 𝓨 d => y - ψDot h)
    with htargetShift_def
  -- IsProbabilityMeasure instances.
  haveI hP_n : ∀ n : ℕ, ∀ θ : Θ k,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun n θ => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Measurability of the rescaling map for each `k_idx`.
  have hg_meas : ∀ k_idx, Measurable
      (fun ω : Fin (n_k k_idx) → 𝓧 =>
        (Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx))) := by
    intro k_idx
    have h_sub : Measurable
        (fun ω : Fin (n_k k_idx) → 𝓧 => T (n_k k_idx) ω - ψ (θ_k k_idx)) :=
      (hT_meas (n_k k_idx)).sub_const _
    exact h_sub.const_smul (Real.sqrt (n_k k_idx))
  -- Each `μs k_idx` is a probability measure.
  haveI hμs_prob : ∀ k_idx, IsProbabilityMeasure (μs k_idx) := by
    intro k_idx
    simp only [hμs_def]
    exact Measure.isProbabilityMeasure_map (hg_meas k_idx).aemeasurable
  -- `(multivariateGaussian h J⁻¹).bind κ` is a probability measure (Markov kernel
  -- composition with a probability measure).
  haveI h_mvg_prob : IsProbabilityMeasure (multivariateGaussian h J⁻¹) := inferInstance
  haveI h_bind_prob :
      IsProbabilityMeasure ((multivariateGaussian h J⁻¹).bind
        (AsymptoticRepresentation.representationKernel J π)) := by
    refine isProbabilityMeasure_bind ?_ ?_
    · exact (AsymptoticRepresentation.representationKernel J π).measurable.aemeasurable
    · refine Filter.Eventually.of_forall ?_
      intro x
      exact inferInstance
  -- The shift map `fun y => y - ψDot h` is continuous and measurable.
  have h_shift_cont : Continuous (fun y : 𝓨 d => y - ψDot h) :=
    continuous_id.sub continuous_const
  have h_shift_meas : Measurable (fun y : 𝓨 d => y - ψDot h) :=
    h_shift_cont.measurable
  -- `targetShift` is therefore a probability measure (push-forward of a probability
  -- measure along a measurable map).
  haveI h_target_prob : IsProbabilityMeasure targetShift := by
    simp only [htargetShift_def]
    exact Measure.isProbabilityMeasure_map h_shift_meas.aemeasurable
  -- Step 1: extract the open-set Portmanteau inequality from `_h_wc_shifted`.
  -- Bridge `WeakConverges` to a `Tendsto` of `ProbabilityMeasure`s.
  let μsPM : ℕ → ProbabilityMeasure (𝓨 d) := fun k_idx => ⟨μs k_idx, inferInstance⟩
  let targetShiftPM : ProbabilityMeasure (𝓨 d) := ⟨targetShift, inferInstance⟩
  have hμsPM_coe : ∀ k_idx, (μsPM k_idx : Measure (𝓨 d)) = μs k_idx := fun _ => rfl
  have htargetPM_coe : (targetShiftPM : Measure (𝓨 d)) = targetShift := rfl
  have h_wc_pm_tendsto :
      Filter.Tendsto μsPM Filter.atTop (𝓝 targetShiftPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp_rw [hμsPM_coe, htargetPM_coe]
    exact _h_wc_shifted f
  -- Open-set Portmanteau inequality (`targetShift G ≤ liminf μs G`).
  have h_opens : ∀ G : Set (𝓨 d), IsOpen G →
      targetShift G ≤ Filter.atTop.liminf (fun k_idx => μs k_idx G) := by
    intro G hG
    have := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_wc_pm_tendsto hG
    simp_rw [hμsPM_coe, htargetPM_coe] at this
    exact this
  -- Step 2: apply the ENNReal-valued LSC Portmanteau bridge with integrand `L`.
  have h_lsc_bridge :
      ∫⁻ z, L z ∂targetShift
        ≤ Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx)) :=
    lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
      hL_lsc h_opens
  -- Step 3: change-of-vars on the LHS:
  -- `∫⁻ y, L (y - ψDot h) ∂κbind = ∫⁻ z, L z ∂(κbind.map (· - ψDot h)) = ∫⁻ z, L z ∂targetShift`.
  have h_LHS_eq :
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π))
        = ∫⁻ z, L z ∂targetShift := by
    simp only [htargetShift_def]
    rw [MeasureTheory.lintegral_map hL_meas h_shift_meas]
  -- Step 4: change-of-vars on each RHS term:
  -- `∫⁻ z, L z ∂(μs k_idx) = ∫⁻ ω, L (rescaled ω) ∂(productMeasure ...)`.
  have h_RHS_term_eq : ∀ k_idx,
      ∫⁻ z, L z ∂(μs k_idx)
        = ∫⁻ ω, L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx)) := by
    intro k_idx
    simp only [hμs_def]
    rw [MeasureTheory.lintegral_map hL_meas (hg_meas k_idx)]
  -- Step 5: rewrite the liminf on the bridge RHS using Step 4.
  have h_RHS_liminf_eq :
      Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx))
        = Filter.atTop.liminf
            (fun k_idx => ∫⁻ ω,
              L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
              ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx))) := by
    congr 1
    funext k_idx
    exact h_RHS_term_eq k_idx
  -- Step 6: `_h_attain` says the (φ ∘ ψ_inner ∘ ρ)-indexed integrand sequence
  -- Tendsto the φ-liminf. By `Tendsto.liminf_eq`, the liminf along atTop of
  -- the same sequence equals that φ-liminf.
  have h_attain_eq :
      Filter.atTop.liminf
        (fun k_idx => ∫⁻ ω,
          L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
          ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx)))
        = Filter.liminf
            (fun k_idx : ℕ =>
              ∫⁻ ω,
                  L ((Real.sqrt (φ k_idx)) •
                        (T (φ k_idx) ω - ψ (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h)))
                ∂(AsymptoticRepresentation.productMeasure M μ
                    (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h) (φ k_idx)))
            Filter.atTop := by
    -- Unfold `θ_k`, `n_k`.
    simp only [hθ_k_def, hn_k_def]
    exact _h_attain.liminf_eq
  -- Step 7: chain everything.
  calc ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
            (AsymptoticRepresentation.representationKernel J π))
      = ∫⁻ z, L z ∂targetShift := h_LHS_eq
    _ ≤ Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx)) := h_lsc_bridge
    _ = Filter.atTop.liminf
          (fun k_idx => ∫⁻ ω,
            L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx))) :=
          h_RHS_liminf_eq
    _ = Filter.liminf
            (fun k_idx : ℕ =>
              ∫⁻ ω,
                  L ((Real.sqrt (φ k_idx)) •
                        (T (φ k_idx) ω - ψ (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h)))
                ∂(AsymptoticRepresentation.productMeasure M μ
                    (θ₀ + (Real.sqrt (φ k_idx))⁻¹ • h) (φ k_idx)))
            Filter.atTop := h_attain_eq

theorem lhs_bound_for_rational_h_via_joint_subseq
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (_hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ)
    (ψ_inner : ℕ → ℕ) (hψ_inner_mono : StrictMono ψ_inner)
    (π : Measure (𝓨 d × Θ k)) [IsProbabilityMeasure π]
    (hπ_conv : WeakConverges
      (fun k_idx => (AsymptoticRepresentation.productMeasure M μ θ₀ (φ (ψ_inner k_idx))).map
        (fun ω => ((Real.sqrt (φ (ψ_inner k_idx))) •
                    (T (φ (ψ_inner k_idx)) ω - ψ θ₀),
                   AsymptoticRepresentation.scoreSum ℓ (φ (ψ_inner k_idx)) ω))) π)
    (h : Θ k)
    (h_rat : ∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) :
    -- Produces a `ρ` bounding LHS by `liminf-along-(φ ∘ ψ_inner ∘ ρ)` (the
    -- sub-sub-sub-sequence's own liminf, attainable via cluster-point extraction).
    -- The outer consumer (`diagonal_subseq_kernel_lift`) bridges to
    -- `localAsymptoticRisk` via the attained sup-over-Finset structure.
    ∃ ρ : ℕ → ℕ, StrictMono ρ ∧
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π))
        ≤ Filter.liminf
            (fun k_idx : ℕ =>
              ∫⁻ ω,
                  L ((Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
                        (T (φ (ψ_inner (ρ k_idx))) ω
                          - ψ (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)))
                ∂(AsymptoticRepresentation.productMeasure M μ
                    (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
                    (φ (ψ_inner (ρ k_idx)))))
            Filter.atTop := by
  classical
  -- A Tendsto-to-`liminf-along-φ-at-h` requirement is mathematically false in
  -- general (a sub-sub-sub-sequence cannot attain the original `φ`-liminf); we
  -- therefore inline the portmanteau-lsc + change-of-vars step (without the
  -- `Tendsto.liminf_eq` step) and produce the weaker but provable
  -- `LHS ≤ liminf-along-(φ ∘ ψ_inner ∘ ρ)` form.
  -- Step 1: cluster-point extract ρ such that `(consumer at φ ∘ ψ_inner ∘ ρ at h)`
  -- Tendsto `liminf (consumer at φ ∘ ψ_inner at h) atTop` (sub-subseq's own liminf).
  set u : ℕ → ℝ≥0∞ := fun k_idx =>
    ∫⁻ ω, L ((Real.sqrt (φ (ψ_inner k_idx))) •
              (T (φ (ψ_inner k_idx)) ω
                - ψ (θ₀ + (Real.sqrt (φ (ψ_inner k_idx)))⁻¹ • h)))
        ∂(AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner k_idx)))⁻¹ • h) (φ (ψ_inner k_idx)))
    with hu_def
  -- ENNReal cluster-point extractor: there exists strict-mono ρ such that
  -- `u ∘ ρ` Tendsto `liminf u atTop`, via
  -- `AsymptoticStatistics.Prohorov.exists_strictMono_tendsto_liminf_ennreal`.
  obtain ⟨ρ, hρ_mono, hρ_tendsto⟩ :=
    AsymptoticStatistics.Prohorov.exists_strictMono_tendsto_liminf_ennreal u
  refine ⟨ρ, hρ_mono, ?_⟩
  -- Step 2: the per-rational-h Le Cam 3 weak conv (along `φ ∘ ψ_inner ∘ ρ`) to
  -- the κ-bind unshifted limit.
  have h_wc_tilted := le_cam_3_per_rational_h_weak_conv M μ θ₀ ℓ hℓ hDQM J hJ
    hJ_fisher ψ T hT_meas hPDF φ hφ_mono ψ_inner
    hψ_inner_mono ρ hρ_mono π (hπ_conv.comp hρ_mono) h h_rat
  have h_kernel_id := representation_kernel_identifies_le_cam_3_limit M μ θ₀ ℓ
    hℓ hDQM J hJ hJ_fisher ψ T hT_meas hPDF φ hφ_mono ψ_inner hψ_inner_mono
    ρ hρ_mono π (hπ_conv.comp hρ_mono) h h_rat
  have h_wc_unshifted : WeakConverges
      (fun k_idx : ℕ =>
        (AsymptoticRepresentation.productMeasure M μ
            (θ₀ + (Real.sqrt (φ (ψ_inner (ρ k_idx))))⁻¹ • h)
            (φ (ψ_inner (ρ k_idx)))).map
          (fun ω => (Real.sqrt (φ (ψ_inner (ρ k_idx)))) •
            (T (φ (ψ_inner (ρ k_idx))) ω - ψ θ₀)))
      ((multivariateGaussian h J⁻¹).bind
        (AsymptoticRepresentation.representationKernel J π)) := by
    rw [← h_kernel_id]; exact h_wc_tilted
  -- Step 3: shift the weak conv to the Fréchet-perturbed consumer form.
  have h_wc_shifted := slutsky_frechet_shift_translation_per_h M μ θ₀ ℓ J hJ
    ψ ψDot hψ_shift T hT_meas hPDF φ hφ_mono ψ_inner hψ_inner_mono ρ
    hρ_mono π h h_rat h_wc_unshifted
  -- Step 4: inline portmanteau-lsc + change-of-vars (without the `Tendsto.liminf_eq`
  -- step) to bound LHS by `liminf-along-(φ ∘ ψ_inner ∘ ρ)`.
  set n_k : ℕ → ℕ := fun k_idx => φ (ψ_inner (ρ k_idx)) with hn_k_def
  set θ_k : ℕ → Θ k := fun k_idx => θ₀ + (Real.sqrt (n_k k_idx))⁻¹ • h with hθ_k_def
  set μs : ℕ → Measure (𝓨 d) :=
    fun k_idx => (AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx)).map
      (fun ω => (Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
    with hμs_def
  set targetShift : Measure (𝓨 d) :=
      ((multivariateGaussian h J⁻¹).bind (AsymptoticRepresentation.representationKernel J π)).map
        (fun y : 𝓨 d => y - ψDot h)
    with htargetShift_def
  haveI hP_n : ∀ n : ℕ, ∀ θ : Θ k,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun n θ => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  have hg_meas : ∀ k_idx, Measurable
      (fun ω : Fin (n_k k_idx) → 𝓧 =>
        (Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx))) := by
    intro k_idx
    have h_sub : Measurable
        (fun ω : Fin (n_k k_idx) → 𝓧 => T (n_k k_idx) ω - ψ (θ_k k_idx)) :=
      (hT_meas (n_k k_idx)).sub_const _
    exact h_sub.const_smul (Real.sqrt (n_k k_idx))
  haveI hμs_prob : ∀ k_idx, IsProbabilityMeasure (μs k_idx) := by
    intro k_idx
    simp only [hμs_def]
    exact Measure.isProbabilityMeasure_map (hg_meas k_idx).aemeasurable
  haveI h_mvg_prob : IsProbabilityMeasure (multivariateGaussian h J⁻¹) := inferInstance
  haveI h_bind_prob :
      IsProbabilityMeasure ((multivariateGaussian h J⁻¹).bind
        (AsymptoticRepresentation.representationKernel J π)) := by
    refine isProbabilityMeasure_bind ?_ ?_
    · exact (AsymptoticRepresentation.representationKernel J π).measurable.aemeasurable
    · refine Filter.Eventually.of_forall ?_
      intro x
      exact inferInstance
  have h_shift_cont : Continuous (fun y : 𝓨 d => y - ψDot h) :=
    continuous_id.sub continuous_const
  have h_shift_meas : Measurable (fun y : 𝓨 d => y - ψDot h) :=
    h_shift_cont.measurable
  haveI h_target_prob : IsProbabilityMeasure targetShift := by
    simp only [htargetShift_def]
    exact Measure.isProbabilityMeasure_map h_shift_meas.aemeasurable
  let μsPM : ℕ → ProbabilityMeasure (𝓨 d) := fun k_idx => ⟨μs k_idx, inferInstance⟩
  let targetShiftPM : ProbabilityMeasure (𝓨 d) := ⟨targetShift, inferInstance⟩
  have hμsPM_coe : ∀ k_idx, (μsPM k_idx : Measure (𝓨 d)) = μs k_idx := fun _ => rfl
  have htargetPM_coe : (targetShiftPM : Measure (𝓨 d)) = targetShift := rfl
  have h_wc_pm_tendsto :
      Filter.Tendsto μsPM Filter.atTop (𝓝 targetShiftPM) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    intro f
    simp_rw [hμsPM_coe, htargetPM_coe]
    exact h_wc_shifted f
  have h_opens : ∀ G : Set (𝓨 d), IsOpen G →
      targetShift G ≤ Filter.atTop.liminf (fun k_idx => μs k_idx G) := by
    intro G hG
    have := MeasureTheory.ProbabilityMeasure.le_liminf_measure_open_of_tendsto
      h_wc_pm_tendsto hG
    simp_rw [hμsPM_coe, htargetPM_coe] at this
    exact this
  have h_lsc_bridge :
      ∫⁻ z, L z ∂targetShift
        ≤ Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx)) :=
    lintegral_le_liminf_lintegral_of_lsc_ennreal_of_forall_isOpen_measure_le_liminf_measure
      hL_lsc h_opens
  have h_LHS_eq :
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
          (AsymptoticRepresentation.representationKernel J π))
        = ∫⁻ z, L z ∂targetShift := by
    simp only [htargetShift_def]
    rw [MeasureTheory.lintegral_map hL_meas h_shift_meas]
  have h_RHS_term_eq : ∀ k_idx,
      ∫⁻ z, L z ∂(μs k_idx)
        = ∫⁻ ω, L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx)) := by
    intro k_idx
    simp only [hμs_def]
    rw [MeasureTheory.lintegral_map hL_meas (hg_meas k_idx)]
  have h_RHS_liminf_eq :
      Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx))
        = Filter.atTop.liminf
            (fun k_idx => ∫⁻ ω,
              L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
              ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx))) := by
    congr 1
    funext k_idx
    exact h_RHS_term_eq k_idx
  calc ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind
            (AsymptoticRepresentation.representationKernel J π))
      = ∫⁻ z, L z ∂targetShift := h_LHS_eq
    _ ≤ Filter.atTop.liminf (fun k_idx => ∫⁻ z, L z ∂(μs k_idx)) := h_lsc_bridge
    _ = Filter.atTop.liminf
          (fun k_idx => ∫⁻ ω,
            L ((Real.sqrt (n_k k_idx)) • (T (n_k k_idx) ω - ψ (θ_k k_idx)))
            ∂(AsymptoticRepresentation.productMeasure M μ (θ_k k_idx) (n_k k_idx))) :=
          h_RHS_liminf_eq

/-- **Kernel witness + per-h liminf-attaining sub-subseq** (rational-h restriction).

The inner content of `subseq_lan_per_h_liminf_along_diagonal`: produces a
single Markov kernel `κ` (h-independent) such that for **each rational** `h`,
there exists a sub-subseq `τ : ℕ → ℕ` (h-dependent) along which the LHS
`∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ)` is bounded by the liminf of the
consumer-side integral.

**Rational restriction**: a single h-independent κ combined with a σ_h-attainer
of `liminf-along-φ` is incompatible at all `h : Θ k`. The κ comes from a single
Prokhorov diagonal sub-sequence on the joint pushforward; one cannot demand that
for every `h`, a further sub-sub-sequence attains that `h`'s φ-liminf unless `h`
ranges over a countable dense set where the diagonal extraction applies.
Restriction to rational `h` (the form `(WithLp.equiv 2 _).symm (q : Fin k → ℚ)`)
makes the chain feasible: a countable rational set permits countable diagonal
extraction, so σ_h attainment holds. The downstream consumer
`diagonal_subseq_kernel_lift` already uses only rational `h`, so this restriction
propagates trivially.

**Mathematical content** (vdV §8.11 along the subseq path):

1. Joint tightness along φ inherits from `hTight` + the score CLT
   (`joint_tightness_T_score_under_P_theta0`).
2. Per-`h` liminf attainer: for each h, the φ-indexed consumer-side integral
   sequence has a cluster point at `liminf-along-φ` (ENNReal is sequentially
   compact); extract σ_h attaining it.
3. Joint Prokhorov along φ ∘ σ_h: joint tightness still holds along (φ ∘ σ_h);
   extract τ_h further so that the joint pushforward weakly converges. The joint
   pushforward `(P^n_θ₀).map((√n(T-ψθ₀), Δ_n))` is under `P^n_θ₀` (not
   `P^n_{θ₀+h/√n}`), so the tightness is h-independent.
4. Kernel construction: π is the joint limit; π's second marginal is
   `multivariateGaussian 0 J` (score CLT half + uniqueness of weak limit);
   `κ := representationKernel J π` is the Markov kernel.
5. Le Cam 3 + Theorem 8.3 along φ ∘ σ_h ∘ τ_h: per h, `(P^{...}).map(√n
   (T-ψθ₀)) ⇝ (mvg h J⁻¹).bind κ`.
6. Slutsky-Fréchet shift: combining with `√n(ψ(θ₀+h/√n) - ψθ₀) → ψDot h`,
   `(P^{...}).map(√n(T - ψ(θ₀+h/√n))) ⇝ ((mvg h J⁻¹).bind κ).map(· - ψDot h)`.
7. Portmanteau-lsc + change-of-vars: for lsc L, `∫⁻ L(y - ψDot h) d((mvg h
   J⁻¹).bind κ) = ∫⁻ L d(((mvg h J⁻¹).bind κ).map(· - ψDot h)) ≤ liminf-along-
   (φ ∘ σ_h ∘ τ_h) (consumer-side integral)`. Since σ_h is attaining and τ_h
   is a further sub-subseq, `liminf-along-(φ ∘ σ_h ∘ τ_h) ≤ liminf-along-φ`.

**Why κ is h-independent**: (a) the joint pushforward sequence
`(P^n_θ₀).map((√n(T-ψθ₀), Δ_n))` is h-independent (under the central measure
`P^n_θ₀`); (b) its weak limit π is consequently h-independent up to choice of
sub-subseq; (c) `representationKernel J π` is a function of π only. The per-h
σ_h, τ_h all give sub-subseqs of the same joint-limit sub-subseq family, so the
κ extracted via the outer (h-independent) sub-subseq is fixed once and for all.
Extension to all `h` via `F_lsc_in_h` is handled by the consumer. -/
theorem subseq_lan_per_h_LHS_bound_witness
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ) :
    -- Produces a `τ` bounding LHS by `liminf-along-(φ ∘ τ)-at-h`. The outer chain
    -- (`subseq_lan_per_h_liminf_along_diagonal` → attainer → sup-over-Finset
    -- bridge) converts to `≤ localAsymptoticRisk`.
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k,
        (∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) →
        ∃ τ : ℕ → ℕ, StrictMono τ ∧
          ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
            ≤ Filter.liminf
                (fun k_idx : ℕ =>
                  ∫⁻ ω,
                      L ((Real.sqrt (φ (τ k_idx))) •
                            (T (φ (τ k_idx)) ω
                              - ψ (θ₀ + (Real.sqrt (φ (τ k_idx)))⁻¹ • h)))
                    ∂(AsymptoticRepresentation.productMeasure M μ
                        (θ₀ + (Real.sqrt (φ (τ k_idx)))⁻¹ • h) (φ (τ k_idx))))
                Filter.atTop := by
  classical
  -- IsProbabilityMeasure instances for each productMeasure (from hPDF).
  haveI : ∀ θ : Θ k, ∀ n,
      IsProbabilityMeasure (AsymptoticRepresentation.productMeasure M μ θ n) :=
    fun θ n => AsymptoticRepresentation.productMeasure_isProbabilityMeasure M μ hPDF θ n
  -- Step 1: joint tightness of the consumer-side + score-side under `P^n_θ₀`.
  have hJoint_tight :=
    joint_tightness_T_score_under_P_theta0 M μ θ₀ ℓ hℓ hDQM J hJ_fisher
      ψ T hT_meas hTight hPDF
  -- Joint sequence shape along ℕ.
  let jointSeq : ℕ → Measure (𝓨 d × Θ k) := fun n =>
    (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
      (fun ω => ((Real.sqrt n) • (T n ω - ψ θ₀),
                 AsymptoticRepresentation.scoreSum ℓ n ω))
  -- Step 2: Subsample along φ — tightness preserved.
  have hJoint_tight_phi : MeasureTheory.IsTightMeasureSet
      (Set.range (fun k_idx : ℕ => jointSeq (φ k_idx))) := by
    refine hJoint_tight.subset ?_
    rintro ν ⟨k_idx, rfl⟩
    exact ⟨φ k_idx, rfl⟩
  -- Score measurability used downstream.
  have h_score_meas : ∀ n, Measurable (AsymptoticRepresentation.scoreSum ℓ n) := fun n => by
    unfold AsymptoticRepresentation.scoreSum
    exact (Finset.univ.measurable_sum
      (fun i _ => hℓ.comp (measurable_pi_apply i))).const_smul
      ((Real.sqrt (n : ℝ))⁻¹ : ℝ)
  have h_T_n_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      (Real.sqrt n) • (T n ω - ψ θ₀)) := fun n =>
    ((hT_meas n).sub_const _).const_smul (Real.sqrt n)
  have h_pair_meas : ∀ n, Measurable (fun ω : Fin n → 𝓧 =>
      ((Real.sqrt n) • (T n ω - ψ θ₀), AsymptoticRepresentation.scoreSum ℓ n ω)) :=
    fun n => (h_T_n_meas n).prodMk (h_score_meas n)
  haveI hJointSeq_prob : ∀ n, IsProbabilityMeasure (jointSeq n) := by
    intro n
    exact MeasureTheory.Measure.isProbabilityMeasure_map (h_pair_meas n).aemeasurable
  haveI hJointPhi_prob : ∀ k_idx, IsProbabilityMeasure (jointSeq (φ k_idx)) :=
    fun k_idx => hJointSeq_prob (φ k_idx)
  -- Step 3: Apply Prokhorov on the φ-subseq joint to extract a sub-subseq + π.
  obtain ⟨ψ_inner, hψ_inner_mono, π, hπ_prob, hπ_conv⟩ :=
    AsymptoticStatistics.Prohorov.extract_weak_subseq
      (fun k_idx => jointSeq (φ k_idx)) hJoint_tight_phi
  -- Step 4: Define κ := representationKernel J π.
  refine ⟨AsymptoticRepresentation.representationKernel J π, inferInstance, ?_⟩
  -- Step 5: per rational h, invoke the substantive measure-theoretic chain.
  -- The chain produces a per-`h` `ρ` and `LHS ≤ liminf-along-(φ ∘ ψ_inner ∘ ρ)`.
  -- Compose `τ := ψ_inner ∘ ρ` to match the outer-witness conclusion shape.
  intro h h_rat
  obtain ⟨ρ, hρ_mono, h_LHS_bound⟩ :=
    lhs_bound_for_rational_h_via_joint_subseq M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
      ψ ψDot hψ_shift T hT_meas L hL_meas hL_lsc hTight hPDF
      φ hφ_mono ψ_inner hψ_inner_mono π hπ_conv h h_rat
  refine ⟨ψ_inner ∘ ρ, hψ_inner_mono.comp hρ_mono, ?_⟩
  -- The conclusion's liminf is over `φ (τ k_idx) = φ (ψ_inner (ρ k_idx))` — matches
  -- `h_LHS_bound`'s RHS by definitional equality.
  exact h_LHS_bound

/-- Kernel witness wrapper; forwards to `subseq_lan_per_h_LHS_bound_witness`
(the substantive measure-theoretic chain). See the section docstring for the
rational-restriction structural diagnosis. -/
theorem subseq_lan_per_h_kernel_witness
    {k d : ℕ} {𝓧 : Type*} [MeasurableSpace 𝓧]
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ) :
    -- Bounds `LHS_h ≤ liminf-along-(φ ∘ σ)-at-h`. No `Tendsto`-to-`liminf-along-φ`
    -- clause: a subsequence's liminf is ≥ the original's, with equality not forced.
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k,
        (∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
            ≤ Filter.liminf
                (fun k_idx : ℕ =>
                  ∫⁻ ω,
                      L ((Real.sqrt (φ (σ k_idx))) •
                            (T (φ (σ k_idx)) ω
                              - ψ (θ₀ + (Real.sqrt (φ (σ k_idx)))⁻¹ • h)))
                    ∂(AsymptoticRepresentation.productMeasure M μ
                        (θ₀ + (Real.sqrt (φ (σ k_idx)))⁻¹ • h) (φ (σ k_idx))))
                Filter.atTop := by
  classical
  -- Forward directly to `subseq_lan_per_h_LHS_bound_witness`, which already
  -- exposes `τ` and provides the LHS-bound in the required shape.
  obtain ⟨κ, hκ_Markov, h_witness⟩ :=
    subseq_lan_per_h_LHS_bound_witness M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
      ψ ψDot hψ_shift T hT_meas L hL_meas hL_lsc hTight
      hPDF φ hφ_mono
  exact ⟨κ, hκ_Markov, h_witness⟩

/-- **Subseq-LAN + Le Cam 3 + Slutsky/Fréchet + Portmanteau-lsc**
along a pre-given diagonal sub-sequence (rational-h restriction).

The outer wrapper: given the substantive content of
`subseq_lan_per_h_kernel_witness` (κ + per-rational-h liminf-attaining σ_h +
per-rational-h bound LHS ≤ liminf-along-σ_h).

**Rational restriction**: the conclusion is gated by
`(∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (q : Fin k → ℝ))`. See
`subseq_lan_per_h_kernel_witness` for the structural diagnosis that forces this
restriction (a single κ + σ_h-attaining-of-`liminf-along-φ` is infeasible at
arbitrary `h`). Downstream `diagonal_subseq_kernel_lift` already consumes only
rational `h`, so the restriction propagates trivially. -/
theorem subseq_lan_per_h_liminf_along_diagonal
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ)
    (φ : ℕ → ℕ) (hφ_mono : StrictMono φ) :
    -- Bounds `LHS_h ≤ liminf-along-(φ ∘ σ)-at-h`. The outer caller bridges
    -- to `localAsymptoticRisk` via the attainer + sup-over-Finset chain.
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k,
        (∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) →
        ∃ σ : ℕ → ℕ, StrictMono σ ∧
          ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
            ≤ Filter.liminf
                (fun k_idx : ℕ =>
                  ∫⁻ ω,
                      L ((Real.sqrt (φ (σ k_idx))) •
                            (T (φ (σ k_idx)) ω
                              - ψ (θ₀ + (Real.sqrt (φ (σ k_idx)))⁻¹ • h)))
                    ∂(AsymptoticRepresentation.productMeasure M μ
                        (θ₀ + (Real.sqrt (φ (σ k_idx)))⁻¹ • h) (φ (σ k_idx))))
                Filter.atTop := by
  classical
  -- Forward to the inner kernel-witness helper.
  obtain ⟨κ, hκ_Markov, h_inner⟩ :=
    subseq_lan_per_h_kernel_witness M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
      ψ ψDot hψ_shift T hT_meas L hL_meas hL_lsc hTight
      hPDF φ hφ_mono
  exact ⟨κ, hκ_Markov, h_inner⟩

/-- **Diagonal-subseq kernel lift.**

The substantive vdV §8.11 chain. The only access route to the limit experiment
is via a Prokhorov sub-sequence (`extract_weak_subseq` returns a `φ : ℕ → ℕ`,
not a full-sequence weak limit), and the literal sup-swap-with-liminf upgrade is
false in general; the proof therefore works along a diagonal sub-sequence.

**Mathematical content** (vdV §8.11):

1. **Joint tightness** of `(√n(T_n - ψ θ₀), score_n)` under `P^n_θ₀`
   (from `joint_tightness_T_score_under_P_theta0`).
2. **Prokhorov sub-sequence extraction** (`extract_weak_subseq`): pick
   a strictly monotone `φ : ℕ → ℕ` along which the joint laws weakly converge
   to a probability measure `π` on `𝓨 d × Θ k`.
3. **Le Cam's 3rd lemma along the subseq**: the joint weak limit determines,
   for each `h ∈ Θ k`, a tilted limit `L_{θ₀,h}` for `(P^φn_{θ₀+h/√φn}).map (√φn ·
   (T_{φn} - ψ θ₀))`.
4. **Theorem 8.3 (`LAN_representation`)**: the tilted limit factors as
   `L_{θ₀,h} = (multivariateGaussian h J⁻¹).bind κ` for a single Markov
   kernel `κ : Kernel (Θ k) (𝓨 d)` (independent of `h`).
5. **Fréchet shift of ψ + Slutsky**: shifts the consumer-side rescaled
   `√n · (T_n - ψ(θ₀+h/√n))` weak limit to `((mvg h J⁻¹).bind κ).map (· - ψDot h)`.
6. **Portmanteau-lsc** on the lsc integrand `y ↦ L(y - ψDot h)` gives the
   per-rational-`h` bound `∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ)
   ≤ localAsymptoticRisk` directly. The rational restriction is necessary
   because Prokhorov gives at most a countable tightness witness (the
   diagonal extraction on the rational lattice), and the lift to all
   `h : Θ k` is done by the consumer via lsc-density.

The conclusion is `≤ localAsymptoticRisk` directly: the diagonal-subseq chain
runs all steps (Prokhorov subseq + Le Cam 3 + Portmanteau-lsc on the singleton
`{h}` Finset) on the same `φ`, so the per-`h` bound is exactly
`≤ localAsymptoticRisk`.

**Body**: assembled from `Prohorov.diagonal_subseq_attaining_lim_sup_finset` +
the subseq-LAN helper `subseq_lan_per_h_liminf_along_diagonal` (carrying the
Prokhorov + Le Cam 3 + Theorem 8.3 + Slutsky-Fréchet + Portmanteau-lsc chain).
For each rational `h₀` the helper supplies
`∫⁻ L(y - ψDot h₀) d((mvg h₀ J⁻¹).bind κ) ≤ liminf_k a(φ k) h₀` along φ, and the
attainment + monotone-chain inclusion `h₀ ∈ I_k₀ ⊆ I_k` (k ≥ k₀) implies
`liminf_k a(φ k) h₀ ≤ liminf_k ⨆_{h ∈ I_k} a(φ k) h = R ≤ localAsymptoticRisk`
(R is the attained limit; ≤ `localAsymptoticRisk` by the Finset-sup definition). -/
theorem diagonal_subseq_kernel_lift
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k) (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ) :
    ∃ κ : Kernel (Θ k) (𝓨 d), IsMarkovKernel κ ∧
      ∀ h : Θ k,
        (∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) →
          ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
            ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
  classical
  -- The per-`n`, per-`h` integrand quantity that appears inside
  -- `localAsymptoticRisk`.
  set a : ℕ → Θ k → ℝ≥0∞ := fun n h =>
    ∫⁻ ω, L ((Real.sqrt n) • (T n ω - ψ (θ₀ + (Real.sqrt n)⁻¹ • h)))
          ∂(AsymptoticRepresentation.productMeasure M μ (θ₀ + (Real.sqrt n)⁻¹ • h) n) with ha_def
  -- `localAsymptoticRisk = ⨆_I, liminf_n ⨆_{h ∈ I} a n h` by definition.
  have h_lar_eq : localAsymptoticRisk M μ θ₀ T ψ L
      = ⨆ I : Finset (Θ k), Filter.liminf
          (fun n : ℕ => ⨆ h ∈ I, a n h) Filter.atTop := rfl
  -- Build the rational enumeration: `Fin k → ℚ` is Countable + Nonempty (use 0),
  -- so there is a surjection `enum : ℕ → (Fin k → ℚ)`.
  haveI : Countable (Fin k → ℚ) := inferInstance
  haveI : Nonempty (Fin k → ℚ) := ⟨fun _ => 0⟩
  obtain ⟨enum, h_enum_surj⟩ := exists_surjective_nat (Fin k → ℚ)
  -- The `n`-th rational coordinate vector in `Θ k`.
  let qVec : ℕ → Θ k := fun n =>
    (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => ((enum n) i : ℝ))
  -- Build the monotone Finset chain `I_k := image qVec {0, 1, ..., k}`
  -- inside `Θ k`. The chain is monotone (k ↦ {0,...,k} is monotone) and
  -- `⋃_k I_k = qVec '' univ`, which contains every rational coordinate vector.
  let I : ℕ → Finset (Θ k) := fun k => (Finset.range (k + 1)).image qVec
  have hI_mono : ∀ k, I k ⊆ I (k + 1) := by
    intro k v hv
    simp only [I, Finset.mem_image, Finset.mem_range] at hv ⊢
    obtain ⟨n, hn, hn_eq⟩ := hv
    refine ⟨n, ?_, hn_eq⟩; omega
  -- Apply the diagonal-attaining subseq extractor.
  obtain ⟨φ, hφ_mono, hφ_tendsto⟩ :=
    Prohorov.diagonal_subseq_attaining_lim_sup_finset (α := Θ k) I hI_mono a
  -- Let `R := ⨆_k liminf_n ⨆_{h ∈ I k} a n h` (the attained limit).
  set R : ℝ≥0∞ := ⨆ k : ℕ, Filter.liminf (fun n => ⨆ h ∈ I k, a n h) Filter.atTop
    with hR_def
  -- `R ≤ localAsymptoticRisk`: each `I_k` is a `Finset (Θ k)`, so the inner
  -- `liminf_n ⨆_{h ∈ I_k} a n h` is bounded by `localAsymptoticRisk` via
  -- the outer `⨆ I : Finset (Θ k)`.
  have hR_le_lar : R ≤ localAsymptoticRisk M μ θ₀ T ψ L := by
    rw [hR_def, h_lar_eq]
    refine iSup_le (fun k₁ => ?_)
    exact le_iSup
      (fun I' : Finset (Θ k) =>
        Filter.liminf (fun n : ℕ => ⨆ h ∈ I', a n h) Filter.atTop) (I k₁)
  -- Apply the subseq-LAN helper along φ. The helper produces a Markov kernel `κ`
  -- and, per rational `h`, a sub-sub-sub-sequence `σ_h`. The bridge to
  -- `localAsymptoticRisk` uses the attainer + sup-over-Finset on the σ_h subseq.
  obtain ⟨κ, hκ_Markov, h_helper⟩ :=
    subseq_lan_per_h_liminf_along_diagonal M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
      ψ ψDot hψ_shift T hT_meas L hL_meas hL_lsc hTight
      hPDF φ hφ_mono
  refine ⟨κ, hκ_Markov, ?_⟩
  -- Now: for each rational `h₀`, unpack the per-h `σ_h₀` + LHS bound;
  -- then bound `liminf-along-(φ ∘ σ_h₀)-at-h₀` by `R` via sup-over-Finset.
  rintro h₀ ⟨q₀, hq₀⟩
  obtain ⟨σ, hσ_mono, h_helper_h₀⟩ := h_helper h₀ ⟨q₀, hq₀⟩
  -- `h₀ = qVec n₀` for `n₀ := encode_inv q₀`.
  obtain ⟨n₀, hn₀⟩ := h_enum_surj q₀
  have hh₀_in_qVec : h₀ = qVec n₀ := by
    simp only [qVec, hq₀, hn₀]
  -- For all `j ≥ n₀`, `h₀ ∈ I j` (since `n₀ ∈ Finset.range (j+1)` when `n₀ ≤ j`).
  have hh₀_in_Ij : ∀ j ≥ n₀, h₀ ∈ I j := by
    intro j hj
    simp only [I, Finset.mem_image, Finset.mem_range]
    exact ⟨n₀, by omega, hh₀_in_qVec.symm⟩
  -- σ is strict-mono on ℕ, so `σ k → ∞`, hence eventually `σ k ≥ n₀`.
  have h_sigma_ge : ∀ᶠ k in Filter.atTop, n₀ ≤ σ k := by
    refine Filter.eventually_atTop.mpr ⟨n₀, fun k hk => ?_⟩
    have : k ≤ σ k := hσ_mono.id_le k
    omega
  -- For each `k` with `σ k ≥ n₀`, `a (φ (σ k)) h₀ ≤ ⨆_{h ∈ I (σ k)} a (φ (σ k)) h`.
  have h_pt_le : ∀ᶠ k in Filter.atTop,
      a (φ (σ k)) h₀ ≤ ⨆ h ∈ I (σ k), a (φ (σ k)) h := by
    refine h_sigma_ge.mono fun k hk => ?_
    exact le_iSup₂_of_le h₀ (hh₀_in_Ij (σ k) hk) le_rfl
  -- Take `liminf_k` of both sides:
  -- `liminf_k a (φ (σ k)) h₀ ≤ liminf_k ⨆_{h ∈ I (σ k)} a (φ (σ k)) h`.
  have h_liminf_le_liminf :
      Filter.liminf (fun k => a (φ (σ k)) h₀) Filter.atTop
        ≤ Filter.liminf (fun k => ⨆ h ∈ I (σ k), a (φ (σ k)) h) Filter.atTop :=
    Filter.liminf_le_liminf h_pt_le
  -- The sub-seq `(k ↦ ⨆_{h ∈ I (σ k)} a (φ (σ k)) h)` is the σ-composition of
  -- `(j ↦ ⨆_{h ∈ I j} a (φ j) h)`, which Tendsto `R`. A sub-seq Tendsto the same
  -- limit, hence its liminf is `R`.
  have h_subseq_tendsto :
      Filter.Tendsto (fun k => ⨆ h ∈ I (σ k), a (φ (σ k)) h) Filter.atTop (𝓝 R) :=
    hφ_tendsto.comp hσ_mono.tendsto_atTop
  have h_subseq_liminf :
      Filter.liminf (fun k => ⨆ h ∈ I (σ k), a (φ (σ k)) h) Filter.atTop = R :=
    h_subseq_tendsto.liminf_eq
  -- Chain: LHS ≤ liminf_k a (φ (σ k)) h₀ ≤ liminf_k ⨆_{h ∈ I (σ k)} a (φ (σ k)) h
  -- = R ≤ localAsymptoticRisk.
  calc ∫⁻ y, L (y - ψDot h₀) ∂((multivariateGaussian h₀ J⁻¹).bind κ)
      ≤ Filter.liminf (fun k => a (φ (σ k)) h₀) Filter.atTop := h_helper_h₀
    _ ≤ Filter.liminf (fun k => ⨆ h ∈ I (σ k), a (φ (σ k)) h) Filter.atTop :=
          h_liminf_le_liminf
    _ = R := h_subseq_liminf
    _ ≤ localAsymptoticRisk M μ θ₀ T ψ L := hR_le_lar

/-- **mvg-bind lsc-Fatou helper** (used by `F_lsc_in_h`).

For any sequence `h_seq → h_lim` in `Θ k`, any Markov kernel `κ : Kernel (Θ k) (𝓨 d)`,
and any nonneg measurable `g : 𝓨 d → ℝ≥0∞`, the lower-semicontinuity-style
inequality

  `∫⁻ y, g y d((multivariateGaussian h_lim J⁻¹).bind κ)`
  `  ≤ liminf_n ∫⁻ y, g y d((multivariateGaussian (h_seq n) J⁻¹).bind κ)`

holds.

**Mathematical content**:

1. **TV-convergence of shifted Gaussians**. The density of
   `multivariateGaussian h J⁻¹` w.r.t. Lebesgue is the explicit Gaussian PDF,
   continuous in `h`. By Scheffé's theorem (pointwise density convergence +
   integrability + Fatou ⇒ L¹ density convergence), `multivariateGaussian (h_seq n) J⁻¹`
   converges to `multivariateGaussian h_lim J⁻¹` in total variation.

2. **TV-contraction by Markov kernel**. For any Markov kernel `κ` and any
   measures `μ, ν` on the source, `‖μ.bind κ - ν.bind κ‖_TV ≤ ‖μ - ν‖_TV`
   (kernel composition is a contraction on signed measures). Hence
   `(multivariateGaussian (h_seq n) J⁻¹).bind κ → (multivariateGaussian h_lim J⁻¹).bind κ`
   in total variation.

3. **TV-conv + bounded approximation ⇒ lsc-Fatou for nonneg measurable**.
   For bounded measurable `g_M := g ⊓ M`, TV-conv gives
   `∫⁻ g_M dν_n → ∫⁻ g_M dν_lim`. Since `g_M ≤ g`, `∫⁻ g_M dν_lim ≤ liminf_n ∫⁻ g dν_n`.
   Take `⨆ M` and apply MCT to recover `g`.

**Why no `κ`-Feller**: TV-conv of the marginals (step 1) is strictly stronger
than weak conv, and step 2 (TV-contraction) does not require any continuity
of `κ`. Hence this helper closes without `[FellerKernel κ]`. -/
theorem mvg_bind_lsc_Fatou_helper
    {k d : ℕ} (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (κ : Kernel (Θ k) (𝓨 d)) [IsMarkovKernel κ]
    (h_seq : ℕ → Θ k) (h_lim : Θ k)
    (h_tend : Filter.Tendsto h_seq Filter.atTop (𝓝 h_lim))
    (g : 𝓨 d → ℝ≥0∞) (hg_meas : Measurable g) :
    ∫⁻ y, g y ∂((multivariateGaussian h_lim J⁻¹).bind κ) ≤
      Filter.atTop.liminf
        (fun n => ∫⁻ y, g y ∂((multivariateGaussian (h_seq n) J⁻¹).bind κ)) := by
  classical
  -- Abbreviations.
  set H : Θ k → ℝ≥0∞ := fun θ => ∫⁻ y, g y ∂κ θ with hH_def
  have hH_meas : Measurable H := hg_meas.lintegral_kernel
  -- `hJ.inv : J⁻¹.PosDef`, hence `J⁻¹.PosSemidef`.
  have hJinv : J⁻¹.PosDef := hJ.inv
  have hJinv_psd : J⁻¹.PosSemidef := hJinv.posSemidef
  -- `J⁻¹ * J = 1` via `hJ.isUnit ⇒ IsUnit J.det`.
  have hJ_det_unit : IsUnit J.det := (Matrix.isUnit_iff_isUnit_det _).mp hJ.isUnit
  have h_inv_mul_J : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hJ_det_unit
  -- The CLM `toEuclideanCLM J : Θ k →L[ℝ] Θ k` is continuous (its bundled `.toCLM`).
  set Jh : Θ k → Θ k := fun h => Matrix.toEuclideanCLM (𝕜 := ℝ) J h with hJh_def
  have hJh_cont : Continuous Jh := by
    have := (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin k) J).continuous
    simpa [hJh_def] using this
  -- Identity: `toEuclideanCLM J⁻¹ ∘ toEuclideanCLM J = id` on Θ k.
  have h_toCLM_id : ∀ h : Θ k,
      Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ (Jh h) = h := by
    intro h
    change (Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹
              * Matrix.toEuclideanCLM (𝕜 := ℝ) J) h = h
    rw [← map_mul, h_inv_mul_J, map_one]; rfl
  -- Rewrite the dot-product `(Jh h).ofLp ⬝ᵥ J⁻¹.mulVec (Jh h).ofLp` as `⟪Jh h, h⟫`
  -- (the Mathlib density form unfolded through `inner_toEuclideanCLM` + `h_toCLM_id`).
  have h_dotProd_eq : ∀ h : Θ k,
      (Jh h).ofLp ⬝ᵥ J⁻¹.mulVec (Jh h).ofLp = ⟪Jh h, h⟫ := by
    intro h
    have hmat : (Jh h).ofLp ⬝ᵥ J⁻¹.mulVec (Jh h).ofLp
        = ⟪Jh h, Matrix.toEuclideanCLM (𝕜 := ℝ) J⁻¹ (Jh h)⟫ :=
      (Matrix.inner_toEuclideanCLM J⁻¹ (Jh h) (Jh h)).symm
    rw [hmat, h_toCLM_id]
  -- The density at parameter `h`, evaluated at `θ ∈ Θ k`.
  set φ : Θ k → Θ k → ℝ≥0∞ := fun h θ =>
      ENNReal.ofReal (Real.exp (⟪Jh h, θ⟫ - ⟪Jh h, h⟫ / 2)) with hφ_def
  -- Helper: `mvg h J⁻¹ = (mvg 0 J⁻¹).withDensity (φ h)` via the Mathlib shift identity.
  have hMvgShift : ∀ h : Θ k,
      multivariateGaussian h J⁻¹
        = (multivariateGaussian (0 : Θ k) J⁻¹).withDensity (φ h) := by
    intro h
    have h_shift := multivariateGaussian_withDensity_exp_shift hJinv_psd (Jh h)
    rw [h_toCLM_id] at h_shift
    -- Rewrite the density in `h_shift` to match `φ h` form.
    have h_density_eq :
        (fun y : Θ k => ENNReal.ofReal (Real.exp (⟪Jh h, y⟫
            - ((Jh h).ofLp ⬝ᵥ J⁻¹.mulVec (Jh h).ofLp) / 2)))
          = φ h := by
      funext y
      simp only [hφ_def, h_dotProd_eq h]
    rw [h_density_eq] at h_shift
    exact h_shift.symm
  -- Continuity in `h` of `φ h θ` for each fixed θ — for the Fatou liminf step.
  have hφ_cont : ∀ θ : Θ k, Continuous (fun h : Θ k => φ h θ) := by
    intro θ
    refine ENNReal.continuous_ofReal.comp ?_
    refine Real.continuous_exp.comp ?_
    -- `h ↦ ⟪Jh h, θ⟫` continuous (CLM + inner).
    have h_inner1 : Continuous (fun h : Θ k => ⟪Jh h, θ⟫) :=
      (continuous_id.inner continuous_const).comp hJh_cont
    -- `h ↦ ⟪Jh h, h⟫` continuous (bilinear inner of two continuous arguments).
    have h_inner2 : Continuous (fun h : Θ k => ⟪Jh h, h⟫) :=
      hJh_cont.inner continuous_id
    exact h_inner1.sub (h_inner2.div_const 2)
  -- Measurability of `φ h` in θ — used both for the withDensity-mul rewrite and Fatou.
  have hφh_meas : ∀ h : Θ k, Measurable (φ h) := by
    intro h
    simp only [hφ_def]
    refine ENNReal.measurable_ofReal.comp ?_
    refine Real.continuous_exp.measurable.comp ?_
    have h_inner_meas : Measurable (fun θ : Θ k => ⟪Jh h, θ⟫) :=
      (continuous_const.inner continuous_id).measurable
    have h_const_meas : Measurable (fun _ : Θ k => ⟪Jh h, h⟫ / 2) :=
      measurable_const
    exact h_inner_meas.sub h_const_meas
  -- `lintegral_bind` to reduce both sides to integrals on Θ k of H against mvg h J⁻¹.
  have hKernel_aem : ∀ h : Θ k, AEMeasurable (κ ·) (multivariateGaussian h J⁻¹) :=
    fun _ => κ.measurable.aemeasurable
  have hH_aem_bind : ∀ h : Θ k,
      AEMeasurable g ((multivariateGaussian h J⁻¹).bind κ) :=
    fun _ => hg_meas.aemeasurable
  have h_lintegral_bind : ∀ h : Θ k,
      ∫⁻ y, g y ∂((multivariateGaussian h J⁻¹).bind κ)
        = ∫⁻ θ, H θ ∂(multivariateGaussian h J⁻¹) := by
    intro h
    rw [Measure.lintegral_bind (hKernel_aem h) (hH_aem_bind h)]
  -- Combine bind ⇒ withDensity-mul rewriting.
  have h_unfold : ∀ h : Θ k,
      ∫⁻ y, g y ∂((multivariateGaussian h J⁻¹).bind κ)
        = ∫⁻ θ, φ h θ * H θ ∂(multivariateGaussian (0 : Θ k) J⁻¹) := by
    intro h
    rw [h_lintegral_bind h, hMvgShift h]
    rw [lintegral_withDensity_eq_lintegral_mul _ (hφh_meas h) hH_meas]
    rfl
  rw [h_unfold h_lim]
  -- Right-hand side: rewrite each term via `h_unfold`.
  have h_rhs_eq : (fun n => ∫⁻ y, g y ∂((multivariateGaussian (h_seq n) J⁻¹).bind κ))
      = fun n => ∫⁻ θ, φ (h_seq n) θ * H θ ∂(multivariateGaussian (0 : Θ k) J⁻¹) := by
    funext n; exact h_unfold (h_seq n)
  rw [h_rhs_eq]
  -- Apply Fatou (`lintegral_liminf_le`) on the fixed measure `mvg 0 J⁻¹`.
  -- We need pointwise: `φ h_lim θ * H θ ≤ liminf_n (φ (h_seq n) θ * H θ)`.
  have hφ_lim_neTop : ∀ θ : Θ k, φ h_lim θ ≠ ∞ := by
    intro θ; simp only [hφ_def]; exact ENNReal.ofReal_ne_top
  have h_pointwise : ∀ θ : Θ k,
      φ h_lim θ * H θ ≤ Filter.atTop.liminf (fun n => φ (h_seq n) θ * H θ) := by
    intro θ
    -- φ (h_seq n) θ → φ h_lim θ in ENNReal (continuity of `h ↦ φ h θ`).
    have h_cont_θ : Continuous (fun h : Θ k => φ h θ) := hφ_cont θ
    have h_tend_φ : Filter.Tendsto (fun n => φ (h_seq n) θ) Filter.atTop
        (𝓝 (φ h_lim θ)) := (h_cont_θ.tendsto h_lim).comp h_tend
    -- Split on whether `H θ = ∞`.
    by_cases hH_inf : H θ = ∞
    · -- Case `H θ = ∞`. If `φ h_lim θ = 0`, LHS = 0 ≤ anything.
      -- Otherwise `φ h_lim θ ≠ 0`; by continuity `φ (h_seq n) θ` is `> 0` eventually,
      -- so `φ (h_seq n) θ * ∞ = ∞` eventually; liminf = ∞ = LHS.
      rw [hH_inf]
      by_cases hφ_zero : φ h_lim θ = 0
      · simp [hφ_zero]
      · -- Use `Tendsto.mul_const` with disjunct `a ≠ 0`.
        have h_tend_prod : Filter.Tendsto (fun n => φ (h_seq n) θ * ∞) Filter.atTop
            (𝓝 (φ h_lim θ * ∞)) := ENNReal.Tendsto.mul_const h_tend_φ (Or.inl hφ_zero)
        exact h_tend_prod.liminf_eq.symm.le
    · -- Case `H θ ≠ ∞`. Use `Tendsto.mul_const` with disjunct `b ≠ ∞`.
      have h_tend_prod : Filter.Tendsto (fun n => φ (h_seq n) θ * H θ) Filter.atTop
          (𝓝 (φ h_lim θ * H θ)) := ENNReal.Tendsto.mul_const h_tend_φ (Or.inr hH_inf)
      exact h_tend_prod.liminf_eq.symm.le
  -- Construct measurability of integrand `(fun n θ => φ (h_seq n) θ * H θ)` in θ.
  have h_meas_n : ∀ n, Measurable (fun θ => φ (h_seq n) θ * H θ) := by
    intro n; exact (hφh_meas (h_seq n)).mul hH_meas
  -- Fatou step:
  --   ∫⁻ θ, φ h_lim θ * H θ d(mvg 0 J⁻¹)
  --     ≤ ∫⁻ θ, liminf_n (φ (h_seq n) θ * H θ) d(mvg 0 J⁻¹) -- by lintegral_mono
  --     ≤ liminf_n ∫⁻ θ, φ (h_seq n) θ * H θ d(mvg 0 J⁻¹). -- by lintegral_liminf_le
  refine le_trans ?_ (lintegral_liminf_le h_meas_n)
  refine lintegral_mono ?_
  intro θ
  exact h_pointwise θ

/-- **lsc of the bind-loss integrand in `h`**.

For a Markov kernel `κ : Kernel (Θ k) (𝓨 d)` and a lsc loss `L`, the
parameterised integral

  `F(h) := ∫⁻ y, L(y - ψDot h) d((multivariateGaussian h J⁻¹).bind κ)(y)`

is lower semi-continuous in `h : Θ k`.

**Why it's true**:
1. `mvg h_n J⁻¹ → mvg h_∞ J⁻¹` in *total variation* as `h_n → h_∞`. This is
   the Scheffé argument applied to the Gaussian densities (pointwise
   convergence + dominated convergence + L¹ → TV).
2. TV convergence is preserved under `.bind κ` for any Markov `κ` (trivial:
   `|(μ.bind κ)(A) - (ν.bind κ)(A)| ≤ ‖μ - ν‖_TV` uniformly in `A`).
3. Combined with pointwise lsc of `y ↦ L(y - ψDot h)` in `h` (lsc-Portmanteau
   on the diagonal, layer-cake + `inf_{k≥n} f_k` monotone-trick to combine
   moving integrand with TV-convergent measure).

**Why no Feller hypothesis on `κ` is needed**: the Gaussian-shift structure of
`mvg h J⁻¹` (translation of `mvg 0 J⁻¹` with smooth density dependence on `h`)
gives TV convergence of the marginals, which is strong enough to push `.bind κ`
through without requiring `κ`-side continuity.

The structural reduction (sequential-closed-preimage + monotone-decomposition)
consumes the TV-conv-of-bind step via `mvg_bind_lsc_Fatou_helper`. -/
theorem F_lsc_in_h
    {k d : ℕ} (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (κ : Kernel (Θ k) (𝓨 d)) [IsMarkovKernel κ] :
    LowerSemicontinuous (fun h : Θ k =>
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)) := by
  -- Abbreviate the parameterised integral.
  set F : Θ k → ℝ≥0∞ := fun h =>
    ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ) with hF_def
  -- Measurability of `y ↦ L(y - ψDot h)` for each `h`, needed for Fatou.
  have hL_shift_meas : ∀ h : Θ k, Measurable (fun y : 𝓨 d => L (y - ψDot h)) := by
    intro h
    exact hL_meas.comp (measurable_id.sub_const (ψDot h))
  -- For each fixed `y`, `h ↦ L(y - ψDot h)` is lsc (composition of lsc and
  -- continuous): `ψDot` is a continuous linear map, hence continuous in `h`;
  -- subtraction from `y` is continuous; `L` is lsc.
  have hL_pull_lsc : ∀ y : 𝓨 d, LowerSemicontinuous (fun h : Θ k => L (y - ψDot h)) := by
    intro y
    exact hL_lsc.comp (continuous_const.sub ψDot.continuous)
  -- Reduce to closed-sublevel-set criterion (`ℝ≥0∞` is a linear order).
  refine lowerSemicontinuous_iff_isClosed_preimage.mpr ?_
  intro c
  -- `Θ k = EuclideanSpace ℝ (Fin k)` is metrisable hence a `SequentialSpace`;
  -- a set is closed iff it is sequentially closed.
  refine isSeqClosed_iff_isClosed.mp ?_
  intro h_seq h_lim h_mem h_tend
  -- `h_mem n : F (h_seq n) ≤ c`; `h_tend : Tendsto h_seq atTop (𝓝 h_lim)`.
  -- Goal: `F h_lim ≤ c`.
  change F h_lim ≤ c
  -- Step 1: pointwise sequential lsc — for each `y`,
  --   `L(y - ψDot h_lim) ≤ liminf_n L(y - ψDot (h_seq n))`.
  have h_pt : ∀ y : 𝓨 d,
      L (y - ψDot h_lim) ≤ Filter.atTop.liminf (fun n => L (y - ψDot (h_seq n))) := by
    intro y
    have h_lsc_y : LowerSemicontinuous (fun h : Θ k => L (y - ψDot h)) := hL_pull_lsc y
    have h_filter : L (y - ψDot h_lim) ≤
        Filter.liminf (fun h : Θ k => L (y - ψDot h)) (𝓝 h_lim) :=
      h_lsc_y.le_liminf h_lim
    refine h_filter.trans ?_
    have hmap : Filter.map h_seq Filter.atTop ≤ 𝓝 h_lim := h_tend
    have h_le := Filter.liminf_le_liminf_of_le (β := ℝ≥0∞)
      (u := fun h : Θ k => L (y - ψDot h)) hmap
    have h_rewrite :
        Filter.liminf (fun h : Θ k => L (y - ψDot h)) (Filter.map h_seq Filter.atTop)
          = Filter.atTop.liminf (fun n => L (y - ψDot (h_seq n))) := by
      simp [Filter.liminf, Filter.limsInf, Filter.map_map, Function.comp]
    rw [h_rewrite] at h_le
    exact h_le
  --   `g_m(y) := ⨅_{n ≥ m} L(y - ψDot (h_seq n))`. Each `g_m` is measurable
  --   (countable inf of measurable), `g_m ≤ L(· - ψDot (h_seq n))` for `n ≥ m`,
  --   and `⨆_m g_m = liminf_n L(· - ψDot (h_seq n)) ≥ L(· - ψDot h_lim)` pointwise.
  set g : ℕ → 𝓨 d → ℝ≥0∞ := fun m y => ⨅ n : {n : ℕ // m ≤ n}, L (y - ψDot (h_seq n)) with hg_def
  -- Measurability of `g m`.
  have hg_meas : ∀ m, Measurable (g m) := by
    intro m
    simp only [hg_def]
    exact Measurable.iInf (fun n => hL_shift_meas (h_seq (n : ℕ)))
  -- `g m` is monotone in `m`: `g m ≤ g (m+1)` since the inf is over a smaller set.
  have hg_mono : Monotone g := by
    intro m₁ m₂ hm y
    simp only [hg_def]
    refine le_iInf (fun p => ?_)
    refine iInf_le (fun n : {n : ℕ // m₁ ≤ n} =>
      L (y - ψDot (h_seq (n : ℕ)))) ⟨(p : ℕ), hm.trans p.2⟩
  -- `g m y ≤ L(y - ψDot (h_seq n))` for any `n ≥ m`.
  have hg_le_term : ∀ m n : ℕ, m ≤ n → ∀ y, g m y ≤ L (y - ψDot (h_seq n)) := by
    intro m n hmn y
    simp only [hg_def]
    refine iInf_le (fun p : {p : ℕ // m ≤ p} =>
      L (y - ψDot (h_seq (p : ℕ)))) ⟨n, hmn⟩
  -- Pointwise: `⨆_m g m y = liminf_n L(y - ψDot (h_seq n))` (Mathlib idiom).
  have hg_sup_eq_liminf : ∀ y, (⨆ m : ℕ, g m y) =
      Filter.atTop.liminf (fun n => L (y - ψDot (h_seq n))) := by
    intro y
    -- `liminf_n f n = ⨆_m ⨅_{n ≥ m} f n` (standard Mathlib lemma for atTop on ℕ).
    rw [Filter.liminf_eq_iSup_iInf_of_nat]
    -- Now: `⨆ m, ⨅ n : {n // m ≤ n}, L(y - ψDot (h_seq n)) =
    --       ⨆ m, ⨅ n, ⨅ (_ : n ≥ m), L(y - ψDot (h_seq n))`.
    refine iSup_congr (fun m => ?_)
    simp only [hg_def, iInf_subtype, ge_iff_le]
  -- Pointwise `L(· - ψDot h_lim) ≤ ⨆_m g m`.
  have h_pt_sup : ∀ y, L (y - ψDot h_lim) ≤ ⨆ m : ℕ, g m y := by
    intro y
    rw [hg_sup_eq_liminf y]
    exact h_pt y
  -- Step 3: apply the named helper to get
  --   `∫⁻ y, g m y d((mvg h_lim J⁻¹).bind κ) ≤ liminf_n ∫⁻ y, g m y d((mvg (h_seq n) J⁻¹).bind κ)`
  set ν : Θ k → Measure (𝓨 d) := fun h => (multivariateGaussian h J⁻¹).bind κ with hν_def
  have h_helper : ∀ m,
      ∫⁻ y, g m y ∂(ν h_lim) ≤
        Filter.atTop.liminf (fun n => ∫⁻ y, g m y ∂(ν (h_seq n))) := by
    intro m
    exact mvg_bind_lsc_Fatou_helper J hJ κ h_seq h_lim h_tend (g m) (hg_meas m)
  -- Step 4: chain — `∫⁻ g m d ν_n ≤ ∫⁻ L(· - ψDot (h_seq n)) d ν_n` for `n ≥ m`.
  have h_chain : ∀ m,
      Filter.atTop.liminf (fun n => ∫⁻ y, g m y ∂(ν (h_seq n))) ≤
        Filter.atTop.liminf (fun n => ∫⁻ y, L (y - ψDot (h_seq n)) ∂(ν (h_seq n))) := by
    intro m
    refine Filter.liminf_le_liminf ?_
    refine Filter.eventually_atTop.mpr ⟨m, fun n hmn => ?_⟩
    exact lintegral_mono (hg_le_term m n hmn)
  -- Step 5: combine to get `∫⁻ g m d ν_lim ≤ liminf_n F (h_seq n) ≤ c`.
  have h_each_m : ∀ m, ∫⁻ y, g m y ∂(ν h_lim) ≤
      Filter.atTop.liminf (fun n => F (h_seq n)) := by
    intro m
    exact (h_helper m).trans (h_chain m)
  -- Step 6: take sup over `m` and apply MCT.
  -- `(g m)` is monotone increasing, so `⨆_m ∫ g m d ν_lim = ∫ ⨆_m g m d ν_lim` (MCT).
  have h_MCT : (⨆ m : ℕ, ∫⁻ y, g m y ∂(ν h_lim)) =
      ∫⁻ y, ⨆ m : ℕ, g m y ∂(ν h_lim) := by
    rw [lintegral_iSup hg_meas hg_mono]
  -- `F h_lim ≤ ∫⁻ ⨆_m g m d ν_lim` (using pointwise `L(· - ψDot h_lim) ≤ ⨆_m g m`).
  have h_F_le_MCT : F h_lim ≤ ∫⁻ y, ⨆ m : ℕ, g m y ∂(ν h_lim) := by
    refine lintegral_mono (fun y => ?_)
    exact h_pt_sup y
  -- `⨆_m ∫ g m d ν_lim ≤ liminf_n F (h_seq n)` (each summand bounded uniformly).
  have h_sup_le_liminf : (⨆ m : ℕ, ∫⁻ y, g m y ∂(ν h_lim)) ≤
      Filter.atTop.liminf (fun n => F (h_seq n)) := by
    exact iSup_le h_each_m
  -- Chain.
  have h_F_le_liminf : F h_lim ≤ Filter.atTop.liminf (fun n => F (h_seq n)) := by
    refine h_F_le_MCT.trans ?_
    rw [← h_MCT]
    exact h_sup_le_liminf
  -- `liminf_n F (h_seq n) ≤ c` since `F (h_seq n) ≤ c` always.
  refine h_F_le_liminf.trans ?_
  refine Filter.liminf_le_of_le ?_ ?_
  · exact ⟨0, by simp⟩
  · intro b hb
    obtain ⟨n, hn⟩ := hb.exists
    exact hn.trans (h_mem n)

/-- **lsc-density extension of the per-rational-`h` bound to all `h`**.

Given:

* a Markov kernel `κ : Kernel (Θ k) (𝓨 d)`,
* a lsc loss `L`,
* a per-rational-`h` bound `∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ) ≤ M` on
  the dense rational sublattice `{h ∈ Θ k | ∃ q : Fin k → ℚ, h = (q : ℝ)^k}`,

the same bound holds for every `h : Θ k` (with the same constant `M`).

**Proof structure**: pick a rational sequence `y_n → h₀` (mirroring
`iSup_finite_le_iSup_rational_finite_via_lsc`), apply the rational bound
per-`n`, then close via lsc-in-`h` of the integrand (`F_lsc_in_h`) +
`liminf`-monotone.

This helper isolates the lsc-density step from the main consumer chain so
that the consumer's body is purely structural (kernel extraction +
`bowl_shaped_loss_risk_kernel_form` + this helper + `iSup_le`). -/
theorem rational_bound_extends_via_lsc
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (L : 𝓨 d → ℝ≥0∞) (hL_meas : Measurable L) (hL_lsc : LowerSemicontinuous L)
    (κ : Kernel (Θ k) (𝓨 d)) [IsMarkovKernel κ] (M : ℝ≥0∞)
    (h_bound_rat : ∀ h : Θ k,
      (∃ q : Fin k → ℚ, h = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ))) →
        ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ) ≤ M) :
    ∀ h : Θ k,
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ) ≤ M := by
  -- Abbreviate the parameterised integrand.
  set F : Θ k → ℝ≥0∞ := fun h =>
    ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ) with hF_def
  -- lsc-in-`h` is the substantive ingredient, provided by `F_lsc_in_h`.
  have hF_lsc : LowerSemicontinuous F := F_lsc_in_h J hJ ψDot L hL_meas hL_lsc κ
  -- The bound goal is `F h₀ ≤ M`. We prove it by approximating any `h₀ : Θ k`
  -- by a rational sequence `y_n → h₀`, using the rational bound `F (y_n) ≤ M`
  -- for every `n`, and then closing via lsc + `liminf`-monotone.
  intro h₀
  -- Step 1: pick a rational sequence in `Θ k` converging to `h₀`.
  have h_dense_R : DenseRange ((↑) : ℚ → ℝ) := Rat.denseRange_cast
  have h_coord : ∀ i : Fin k, ∃ q : ℕ → ℚ,
      Filter.Tendsto (fun n => ((q n : ℝ))) Filter.atTop
        (𝓝 ((WithLp.equiv 2 (Fin k → ℝ)) h₀ i)) := by
    intro i
    have h_mem : (WithLp.equiv 2 (Fin k → ℝ)) h₀ i ∈ closure (Set.range ((↑) : ℚ → ℝ)) := by
      rw [h_dense_R.closure_range]; trivial
    rcases mem_closure_iff_seq_limit.mp h_mem with ⟨x, hx_mem, hx_tendsto⟩
    choose q hq using hx_mem
    refine ⟨q, ?_⟩
    have h_eq : (fun n => ((q n : ℝ))) = x := by funext n; exact hq n
    rw [h_eq]; exact hx_tendsto
  choose q_seq hq_seq using h_coord
  -- Define the rational sequence in Θ k.
  set y : ℕ → Θ k :=
    fun n => (WithLp.equiv 2 (Fin k → ℝ)).symm (fun i => (q_seq i n : ℝ)) with hy_def
  -- y n → h₀ in Θ k.
  have hy_tendsto : Filter.Tendsto y Filter.atTop (𝓝 h₀) := by
    have h_inner : Filter.Tendsto
        (fun n => (fun i => (q_seq i n : ℝ))) Filter.atTop
        (𝓝 ((WithLp.equiv 2 (Fin k → ℝ)) h₀)) := by
      rw [tendsto_pi_nhds]
      intro i
      exact hq_seq i
    have h_cont : Continuous (fun x : Fin k → ℝ =>
        (WithLp.equiv 2 (Fin k → ℝ)).symm x) :=
      PiLp.continuous_toLp (p := 2) (β := fun _ : Fin k => ℝ)
    exact (h_cont.tendsto _).comp h_inner
  -- y n is rational for each n, so the rational bound applies.
  have hy_rational : ∀ n, ∃ q : Fin k → ℚ,
      y n = (WithLp.equiv 2 _).symm (fun i => (q i : ℝ)) := by
    intro n
    exact ⟨fun i => q_seq i n, by simp [hy_def]⟩
  have hF_y_bound : ∀ n, F (y n) ≤ M := by
    intro n; exact h_bound_rat (y n) (hy_rational n)
  -- Step 2: lsc gives `F h₀ ≤ liminf_n F (y n)`.
  have h_lsc_liminf : F h₀ ≤ Filter.liminf (fun n => F (y n)) Filter.atTop := by
    have h_lsc : F h₀ ≤ Filter.liminf F (𝓝 h₀) := hF_lsc.le_liminf h₀
    have h_map : Filter.map y Filter.atTop ≤ 𝓝 h₀ := hy_tendsto
    have h_le : Filter.liminf F (𝓝 h₀) ≤ Filter.liminf F (Filter.map y Filter.atTop) :=
      Filter.liminf_le_liminf_of_le h_map
    have h_eq : Filter.liminf F (Filter.map y Filter.atTop) =
        Filter.liminf (F ∘ y) Filter.atTop := (Filter.liminf_comp F y _).symm
    exact h_lsc.trans (h_le.trans h_eq.le)
  -- Step 3: `liminf F (y n) ≤ M` since each `F (y n) ≤ M`.
  have h_liminf_le_M : Filter.liminf (fun n => F (y n)) Filter.atTop ≤ M := by
    refine Filter.liminf_le_of_frequently_le ?_
    -- frequently `F (y n) ≤ M` holds (in fact, always — strictly stronger).
    exact Filter.Frequently.of_forall (fun n => hF_y_bound n)
  exact h_lsc_liminf.trans h_liminf_le_M

/-- **`localAsymptoticRisk ≥ target` via the vdV §8.11 chain**.

The direct proof of Theorem 8.11 via the diagonal-subseq + lsc-density chain:

1. Joint tightness of `(√n(T_n - ψθ₀), score_n)` under `P^n_θ₀`.
2. Diagonal-subseq + Le Cam 3 + Theorem 8.3 + Slutsky + Portmanteau-lsc
   gives, on the dense rational sublattice of `Θ k`, a per-rational-`h`
   bound `∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ) ≤ localAsymptoticRisk`
   (`diagonal_subseq_kernel_lift`).
3. lsc-density extension (`rational_bound_extends_via_lsc`): the bound lifts to
   every `h : Θ k`.
4. `bowl_shaped_loss_risk_kernel_form`:
   `target ≤ ⨆ h, ∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ)`.
5. Chain: `target ≤ ⨆ h, (...) ≤ localAsymptoticRisk`.

Relies on `hTight` (vdV §8.11). -/
theorem localAsymptoticRisk_ge_target
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k)
    (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    -- Per-direction functional shift: the rescaled increment
    -- `√n·(ψ(θ₀+h/√n) − ψθ₀) → ψDot h` for each `h`. Weaker than `HasFDerivAt`
    -- (no common modulus / Fréchet requirement, no continuity). The
    -- `local_asymptotic_minimax_bound` wrapper supplies this from `HasFDerivAt`.
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_bowl : BowlShaped L)
    (hL_lsc : LowerSemicontinuous L)
    -- "the sequence √n(T_n − ψ(θ₀)) is uniformly tight under θ₀".
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ) :
    localAsymptoticRisk M μ θ₀ T ψ L
      ≥ ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
                    (ψDotMat * J⁻¹ * ψDotMat.transpose)) := by
  classical
  -- Loss measurability from the BowlShaped bundle.
  have hL_meas : Measurable L := hL_bowl.measurable
  -- Step 1: Apply the diagonal-subseq kernel-lift helper. The chain is
  -- Prokhorov sub-sequence extraction (from joint tightness) + Le Cam 3 +
  -- Theorem 8.3 (LAN_representation) + Slutsky shift + Portmanteau-lsc on the
  -- diagonal sub-sequence indexed by rational `h`'s.
  obtain ⟨κ, hκ_Markov, h_bound_rat⟩ :=
    diagonal_subseq_kernel_lift M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
      ψ ψDot hψ_shift T hT_meas L hL_meas hL_lsc hTight
      hPDF
  -- Step 2: Extend the per-rational-`h` bound to every `h : Θ k` via lsc-density,
  -- wrapped in the `rational_bound_extends_via_lsc` helper.
  have h_bound_full : ∀ h : Θ k,
      ∫⁻ y, L (y - ψDot h) ∂((multivariateGaussian h J⁻¹).bind κ)
        ≤ localAsymptoticRisk M μ θ₀ T ψ L :=
    rational_bound_extends_via_lsc J hJ ψDot L hL_meas hL_lsc κ
      (localAsymptoticRisk M μ θ₀ T ψ L) h_bound_rat
  -- Step 3: `bowl_shaped_loss_risk_kernel_form`
  -- gives `target ≤ ⨆ h, ∫⁻ L(y - ψDot h) d((mvg h J⁻¹).bind κ)`.
  have h_prop_8_6 :
      ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
              (ψDotMat * J⁻¹ * ψDotMat.transpose))
        ≤ ⨆ h : Θ k, ∫⁻ y, L (y - ψDot h)
              ∂((multivariateGaussian h J⁻¹).bind κ) := by
    have := GaussianShiftMinimax.bowl_shaped_loss_risk_kernel_form J hJ ψDot
        ψDot.continuous.measurable
      ψDotMat h_ψDot_mat L hL_meas hL_bowl hL_lsc κ
    exact this
  -- Step 4: chain `target ≤ ⨆ h (...) ≤ localAsymptoticRisk` via `iSup_le`.
  refine le_trans h_prop_8_6 ?_
  exact iSup_le h_bound_full

/-- ## **Theorem 8.11 — Local Asymptotic Minimax Bound, per-direction-shift form.**

Public sibling of `local_asymptotic_minimax_bound` with the weaker functional
hypothesis: instead of Fréchet differentiability `HasFDerivAt ψ ψDot θ₀`, only
the **per-direction rescaled shift** is required,
`√n·(ψ(θ₀ + h/√n) − ψ θ₀) → ψDot h` for each `h`. This is exactly what
`PathwiseDifferentiableAt.derivative_spec` (Gateaux) supplies, with no common
modulus / no Fréchet requirement and no continuity — the o(1/√n) is absorbed
downstream by Slutsky + Portmanteau-lsc. vdV §8.11 only needs this
per-direction expansion (it reworks the bundled reduction to apply Prop 8.6 /
Anderson to the finite-dim submodel). `local_asymptotic_minimax_bound` is the
`HasFDerivAt` wrapper of this theorem.

Body: direct call to `localAsymptoticRisk_ge_target`. -/
theorem local_asymptotic_minimax_bound_of_pointwise_shift
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k)
    (hℓ : Measurable ℓ)
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    -- Per-direction functional shift: `√n·(ψ(θ₀+h/√n) − ψθ₀) →
    -- ψDot h` for each `h`. Weaker than `HasFDerivAt` (no Fréchet, no
    -- continuity); vdV §8.11 reworks the reduction to use only this expansion.
    (hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)))
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    (L : 𝓨 d → ℝ≥0∞)
    (hL_bowl : BowlShaped L)
    (hL_lsc : LowerSemicontinuous L)
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    (hPDF : IsPDFOf M μ) :
    localAsymptoticRisk M μ θ₀ T ψ L
      ≥ ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
                    (ψDotMat * J⁻¹ * ψDotMat.transpose)) :=
  localAsymptoticRisk_ge_target M μ θ₀ ℓ hℓ hDQM J hJ hJ_fisher
    ψ ψDot hψ_shift ψDotMat h_ψDot_mat T hT_meas L hL_bowl hL_lsc
    hTight hPDF

/-- ## **Theorem 8.11 — Local Asymptotic Minimax Bound** (van der Vaart §8.11).

The hypotheses match vdV Thm 8.11 (§8.7). The remaining non-vdV parameters are
pure encoding adapters (`hℓ`, `ψDotMat`/`h_ψDot_mat`, `[SigmaFinite μ]`) plus the
§7 density setup `hPDF`.

Hypotheses (per vdV §8.11):
* `hDQM` — parametric family DQM at θ₀ with score ℓ.
* `hJ`, `hJ_fisher` — Fisher information matrix non-singular.
* `hψ_diff` — target functional ψ Fréchet differentiable at θ₀.
* `hL_bowl`, `hL_lsc` — bowl-shaped + lsc loss.
* `hTight` — `√n(T_n - ψ θ₀)` is uniformly tight under `P^n_θ₀`.
* `hPDF` — vdV §7/§7.2 regularity bundle. (Exact common support is replaced by
  DQM-derived asymptotic singular-mass control.)

Body: direct call to `localAsymptoticRisk_ge_target`. -/
theorem local_asymptotic_minimax_bound
    (M : ParametricFamily 𝓧 (Θ k)) (μ : Measure 𝓧) [SigmaFinite μ]
    (θ₀ : Θ k) (ℓ : 𝓧 → Θ k)
    -- treats the score as automatically measurable; needed in Lean for `ℓ`
    -- inside `lintegral` / kernel constructions. No scope change vs the book.
    (hℓ : Measurable ℓ)
    -- `θ₀` with score `ℓ`; vdV §7.1 / §8.5 (regularity hypothesis at the head
    -- of §8.5 Prop 8.6 and Theorem 8.11).
    (hDQM : DifferentiableQuadraticMean M μ θ₀ ℓ)
    (J : Matrix (Fin k) (Fin k) ℝ) (hJ : J.PosDef)
    (hJ_fisher : ∀ u v : Θ k, fisherInformation M μ θ₀ ℓ u v
      = ⟪u, (WithLp.equiv 2 _).symm (J.mulVec ((WithLp.equiv 2 _) v))⟫)
    -- Target functional `ψ : Θ → ℝ^d`, Fréchet differentiable at `θ₀`:
    (ψ : Θ k → 𝓨 d)
    (ψDot : Θ k →L[ℝ] 𝓨 d)
    (hψ_diff : HasFDerivAt ψ ψDot θ₀)
    -- Matrix form of `ψDot` for the conclusion's covariance:
    (ψDotMat : Matrix (Fin d) (Fin k) ℝ)
    (h_ψDot_mat : ∀ h : Θ k,
      ψDot h = (WithLp.equiv 2 _).symm (ψDotMat.mulVec ((WithLp.equiv 2 _) h)))
    -- Estimator sequence:
    (T : ∀ n, (Fin n → 𝓧) → 𝓨 d) (hT_meas : ∀ n, Measurable (T n))
    -- Loss function: bowl-shaped (symmetric, convex sublevel sets); vdV §8.11.
    (L : 𝓨 d → ℝ≥0∞)
    (hL_bowl : BowlShaped L)
    -- lsc (the Portmanteau-lsc step requires it). For bowl-shaped `L` this is
    -- `L` already equal to its lsc envelope — the typical case of interest.
    (hL_lsc : LowerSemicontinuous L)
    -- "the sequence √n(T_n − ψ(θ₀)) is uniformly tight under θ₀"; vdV §8.11.
    (hTight : MeasureTheory.IsTightMeasureSet
        (Set.range (fun n : ℕ =>
          (AsymptoticRepresentation.productMeasure M μ θ₀ n).map
            (fun ω => (Real.sqrt n) • (T n ω - ψ θ₀)))))
    -- Regularity bundle: the dominating measure `μ`; vdV §7 / §8. The exact
    -- common-support hypothesis transfer routes through the DQM-derived
    -- asymptotic singular-mass control instead of the exact change-of-measure
    -- identity.
    (hPDF : IsPDFOf M μ) :
    localAsymptoticRisk M μ θ₀ T ψ L
      ≥ ∫⁻ y, L y ∂(multivariateGaussian (0 : 𝓨 d)
                    (ψDotMat * J⁻¹ * ψDotMat.transpose)) := by
  -- Derive the per-direction shift `√n·(ψ(θ₀+h/√n) − ψθ₀) → ψDot h` from the
  -- Fréchet derivative `hψ_diff`, then forward to the per-direction sibling.
  have hψ_shift : ∀ h : Θ k, Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀))
      atTop (𝓝 (ψDot h)) := by
    intro h
    -- `sqn n := √n → ∞`.
    have h_sqn_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have h_sqn_pos_event : ∀ᶠ n : ℕ in atTop, 0 < Real.sqrt n :=
      h_sqn_atTop.eventually (eventually_gt_atTop 0)
    have h_sqn_inv_to_zero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
      h_sqn_atTop.inv_tendsto_atTop
    have h_pt_to_θ₀ : Tendsto (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h)
        atTop (𝓝 θ₀) := by
      have hh : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹ • h) atTop (𝓝 0) := by
        simpa using h_sqn_inv_to_zero.smul_const h
      simpa using tendsto_const_nhds.add hh
    -- Fréchet `=o[𝓝 θ₀]` form composed along `n ↦ θ₀ + h/√n`.
    have h_little_o := hψ_diff.isLittleO
    have h_little_o_comp : (fun n : ℕ =>
          ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h))
          =o[atTop] (fun n : ℕ => (Real.sqrt n)⁻¹ • h) := by
      have h_comp := h_little_o.comp_tendsto h_pt_to_θ₀
      have h_lhs_eq : (fun x' => ψ x' - ψ θ₀ - ψDot (x' - θ₀)) ∘
          (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h)
          = (fun n : ℕ =>
            ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h)) := by
        funext n; simp [add_sub_cancel_left]
      have h_rhs_eq : (fun x' => x' - θ₀) ∘
          (fun n : ℕ => θ₀ + (Real.sqrt n)⁻¹ • h)
          = (fun n : ℕ => (Real.sqrt n)⁻¹ • h) := by
        funext n; simp [add_sub_cancel_left]
      rw [h_lhs_eq, h_rhs_eq] at h_comp
      exact h_comp
    -- The shift converges to `0` after subtracting the constant `ψDot h`.
    have h_frechet_shift : Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h)
      atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      set c : ℝ := ε / (‖h‖ + 1) with hc_def
      have hc_pos : 0 < c := by
        have : 0 < ‖h‖ + 1 := by positivity
        positivity
      have hc_bound : c * ‖h‖ < ε := by
        have hh1 : 0 < ‖h‖ + 1 := by positivity
        have := mul_lt_mul_of_pos_left
          (show ‖h‖ < ‖h‖ + 1 by linarith [norm_nonneg h]) hc_pos
        calc c * ‖h‖
            < c * (‖h‖ + 1) := this
          _ = ε := by rw [hc_def, div_mul_cancel₀ _ hh1.ne']
      have h_eventually : ∀ᶠ n : ℕ in atTop,
          ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - ψDot ((Real.sqrt n)⁻¹ • h)‖
            ≤ c * ‖(Real.sqrt n)⁻¹ • h‖ := by
        have := h_little_o_comp.def hc_pos
        simpa using this
      filter_upwards [h_eventually, h_sqn_pos_event] with n h_bound h_sqn_pos
      have h_ψDot_smul : ψDot ((Real.sqrt n)⁻¹ • h)
          = (Real.sqrt n)⁻¹ • ψDot h := by simp
      have h_norm_smul : ‖(Real.sqrt n)⁻¹ • h‖ = (Real.sqrt n)⁻¹ * ‖h‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr h_sqn_pos)]
      have h_smul_factor :
          (Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h
            = (Real.sqrt n) •
              (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀ - (Real.sqrt n)⁻¹ • ψDot h) := by
        rw [smul_sub (Real.sqrt n) (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀)
          ((Real.sqrt n)⁻¹ • ψDot h), smul_inv_smul₀ h_sqn_pos.ne']
      have h_dist_eq :
          dist ((Real.sqrt n) • (ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀) - ψDot h) 0
            = (Real.sqrt n) * ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀
                - ψDot ((Real.sqrt n)⁻¹ • h)‖ := by
        rw [dist_zero_right, h_smul_factor, norm_smul, Real.norm_eq_abs,
          abs_of_pos h_sqn_pos, h_ψDot_smul]
      rw [h_dist_eq]
      calc (Real.sqrt n) * ‖ψ (θ₀ + (Real.sqrt n)⁻¹ • h) - ψ θ₀
                - ψDot ((Real.sqrt n)⁻¹ • h)‖
          ≤ (Real.sqrt n) * (c * ‖(Real.sqrt n)⁻¹ • h‖) :=
            mul_le_mul_of_nonneg_left h_bound h_sqn_pos.le
        _ = (Real.sqrt n) * (c * ((Real.sqrt n)⁻¹ * ‖h‖)) := by rw [h_norm_smul]
        _ = ((Real.sqrt n) * (Real.sqrt n)⁻¹) * (c * ‖h‖) := by ring
        _ = 1 * (c * ‖h‖) := by rw [mul_inv_cancel₀ h_sqn_pos.ne']
        _ = c * ‖h‖ := one_mul _
        _ < ε := hc_bound
    -- Recover the `→ ψDot h` form by adding back the constant.
    have := h_frechet_shift.add_const (ψDot h)
    simpa using this
  exact local_asymptotic_minimax_bound_of_pointwise_shift M μ θ₀ ℓ hℓ hDQM
    J hJ hJ_fisher ψ ψDot hψ_shift ψDotMat h_ψDot_mat T hT_meas L hL_bowl
    hL_lsc hTight hPDF

end LocalAsymptoticMinimax
end AsymptoticStatistics
