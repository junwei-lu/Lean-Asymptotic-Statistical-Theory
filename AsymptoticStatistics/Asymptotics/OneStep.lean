import AsymptoticStatistics.StrictModel.EfficientScore
import AsymptoticStatistics.Core.EfficiencyOperational

/-!
# One-step estimator semiparametric efficiency

Given a `√n`-rate-consistent preliminary estimator `θ̃_n`, the one-step estimator is
`θ̂_n := θ̃_n + (1/n) · Σ_i Î_n⁻¹ · ℓ̂_n(X_i, θ̃_n)`, where `ℓ̂_n` estimates the efficient
score and `Î_n` the efficient information. Under the score-consistency condition (eq:25.55)
and the Donsker / no-bias condition (eq:25.56), `θ̂_n` is asymptotically linear with influence
function `(1 / Ĩ) ℓ̃` and asymptotically efficient.

Reference: vdV §25.5, eqs:25.55, 25.56, 25.58, thm:25.57.

Headline declarations: `OneStepAssumptions`, `oneStep_semiparametricallyEfficient`.

Scope: scalar parameter / 1-dim score direction, matching `SemiparametricallyEfficientAt`
and `eif_from_efficientScore`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace AsymptoticStatistics.Asymptotics.OneStep

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.EfficiencyOperational
open AsymptoticStatistics.StrictModel.EfficientScore

variable {Ω : Type*} [MeasurableSpace Ω]

/-- *Bundled assumptions for vdV thm:25.57 (one-step semiparametric
efficiency).*

Structure parameters: model identity (`S_θ`, `T_nuis`, `v`, `T`, `dψ`)
+ estimator triple (`preliminary`, `score_estimate_seq`,
`info_estimate_seq`) + the one-step combined estimator + centering
`θ₀`. Structure body: the EIF hypotheses + the one-step formula
identity (`estimator_def`) + the empirical-process consequence
(`asympLinear_25_57`).

Reference: vdV §25.5, eqs:25.55, 25.56, 25.58, thm:25.57.

Edge behavior:
* `efficientInformation = 0` ⇒ `hI_pos` fails ⇒ uninhabited (matches
  the standard non-degeneracy convention).
* `info_estimate_seq` having a different limit than `Ĩ` would falsify
  `asympLinear_25_57` rather than the bundle being uninhabited;
  encoded as a downstream-discharged constraint, not a structure
  field. -/
structure OneStepAssumptions
    (P : Measure Ω) [IsProbabilityMeasure P]
    (Θ : Type*) [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    (S_θ : OrdinaryScore P Θ) (T_nuis : NuisanceTangentSpace P)
    [T_nuis.HasOrthogonalProjection] (v : Θ)
    (T : Submodule ℝ ↥(L2ZeroMean P)) (dψ : T →L[ℝ] ℝ)
    (preliminary : ∀ n, (Fin n → Ω) → ℝ)
    (score_estimate_seq : ℕ → Ω → ℝ → ℝ)
    (info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ)
    (estimator : ∀ n, (Fin n → Ω) → ℝ) (θ₀ : ℝ) where
  /-- vdV §25.4 (lem:25.25): the candidate EIF
  `(1 / Ĩ) • ℓ̃` lies in the target tangent space `T`. -/
  h_mem :
    (1 / efficientInformation S_θ T_nuis v)
      • efficientScore S_θ T_nuis v ∈ T
  /-- vdV §25.4 (lem:25.25): `dψ` acts on `T` as
  `(1 / Ĩ) ⟪ℓ̃, ·⟫`. -/
  h_dψ : ∀ g : T,
    dψ g
      = (1 / efficientInformation S_θ T_nuis v)
          * ⟪efficientScore S_θ T_nuis v, (g : ↥(L2ZeroMean P))⟫_ℝ
  /-- vdV §25.4 (lem:25.25): efficient information is
  positive at `v`. -/
  hI_pos : 0 < efficientInformation S_θ T_nuis v
  /-- vdV §25.5 (eq:25.58): the one-step estimator is the
  preliminary plus the empirical correction
  `θ̂_n = θ̃_n + (1/n) · Σ_i Î_n⁻¹ · ℓ̂_n(X_i, θ̃_n)`. Pinning the
  formula in the bundle lets `asympLinear_25_57` reference a known
  algebraic shape, and lets concrete model files prove the AL
  expansion by a one-step Taylor argument on this exact form. -/
  estimator_def : ∀ n (X : Fin n → Ω),
    estimator n X
      = preliminary n X
        + (info_estimate_seq n X)⁻¹
            * ((n : ℝ)⁻¹ * (∑ i, score_estimate_seq n (X i) (preliminary n X)))
  /-- vdV §25.5 (eqs:25.55 + 25.56 + `√n`-rate of the preliminary
  + information consistency `Î_n →_P Ĩ`):

  the one-step estimator `estimator` is asymptotically linear at `P`
  with influence function `(1 / Ĩ) • ℓ̃` and centering `θ₀`. Concrete
  model files prove this from Donsker / Glivenko–Cantelli machinery
  applied to `score_estimate_seq` together with the one-step
  `estimator_def`; the consequence is bundled as a single hypothesis
  to keep the empirical-process layer out of scope.

  Sample-splitting (the half-sample trick) is a proof technique used
  to discharge this field; it is not a separate book theorem. -/
  asympLinear_25_57 :
    AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v)
      θ₀

/-- *vdV thm:25.57 — one-step semiparametric efficiency.*

If the bundled `OneStepAssumptions` holds for the model triple
`(S_θ, T_nuis, v)`, target tangent space `T`, derivative `dψ`, the
preliminary / score / information estimator triple
`(preliminary, score_estimate_seq, info_estimate_seq)`, the combined
one-step estimator `estimator`, and centering `θ₀ = ψ P`, then
`estimator` is semiparametrically efficient at `P` for the parameter
functional `ψ` relative to `T`.

Reference: vdV §25.5, thm:25.57. Sample-splitting is the proof
technique behind the bundled `asympLinear_25_57`, not a separate
theorem.

Proof template:
* **Step A**: produce the EIF via `eif_from_efficientScore`.
* **Step B**: unwrap `asympLinear_25_57` modulo `ψ P = θ₀`.
* **Step C**: combine via
  `estimator_semiparametricallyEfficient_of_asympLinear_eif`.

The empirical-process content of (25.55) + (25.56) + the
preliminary's `√n`-rate is bundled as `asympLinear_25_57` and not
proved here; the one-step formula `eq:25.58` is bundled as
`estimator_def` and likewise not used in this proof (its role is to
shape `asympLinear_25_57` for downstream consumers). -/
theorem oneStep_semiparametricallyEfficient
    {P : Measure Ω} [IsProbabilityMeasure P]
    {Θ : Type*} [NormedAddCommGroup Θ] [InnerProductSpace ℝ Θ] [CompleteSpace Θ]
    {S_θ : OrdinaryScore P Θ} {T_nuis : NuisanceTangentSpace P}
    [T_nuis.HasOrthogonalProjection] {v : Θ}
    {T : Submodule ℝ ↥(L2ZeroMean P)} {dψ : T →L[ℝ] ℝ}
    {preliminary : ∀ n, (Fin n → Ω) → ℝ}
    {score_estimate_seq : ℕ → Ω → ℝ → ℝ}
    {info_estimate_seq : ∀ n, (Fin n → Ω) → ℝ}
    {estimator : ∀ n, (Fin n → Ω) → ℝ} {θ₀ : ℝ}
    (h : OneStepAssumptions P Θ S_θ T_nuis v T dψ
            preliminary score_estimate_seq info_estimate_seq estimator θ₀)
    {ψ : Measure Ω → ℝ} (h_ψ : ψ P = θ₀) :
    SemiparametricallyEfficientAt estimator ψ P T := by
  have hEIF : IsEfficientInfluenceFunction P T dψ
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) :=
    eif_from_efficientScore S_θ T_nuis v T h.h_mem dψ h.h_dψ
  have hAL : AsymptoticallyLinearAt estimator P
      ((1 / efficientInformation S_θ T_nuis v)
        • efficientScore S_θ T_nuis v) (ψ P) := by
    rw [h_ψ]
    exact h.asympLinear_25_57
  exact estimator_semiparametricallyEfficient_of_asympLinear_eif hEIF hAL

end AsymptoticStatistics.Asymptotics.OneStep
