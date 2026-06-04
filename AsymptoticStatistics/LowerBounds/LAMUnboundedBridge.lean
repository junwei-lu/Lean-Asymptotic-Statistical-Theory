import AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
import AsymptoticStatistics.LowerBounds.LAMCanonicalAlign
import AsymptoticStatistics.LowerBounds.LAMUnboundedRecenter
import AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
import AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
import AsymptoticStatistics.ParametricFamily.UnboundedSubmodel
import AsymptoticStatistics.Efficiency.LocalAsymptoticMinimax
import AsymptoticStatistics.LocalAsymptoticNormality.AsymptoticRepresentation

/-!
# LHS inclusion: `localAsymptoticRisk(unbounded, ψ_param_unb) ≤ LHS_canonical`

This file bounds the local-asymptotic-minimax risk over the unbounded sigmoid
submodel by the canonical-path LHS functional `LHS_canonical`, using the **true
submodel functional** `ψ_param_unb θ := ψ(P.withDensity(density θ))` rather than
an affine surrogate.

The construction uses:

* `unboundedParamSubmodel g_P h_orth` — the unbounded sigmoid submodel, which
  works for any `L²`-zero-mean orthonormal basis (no bounded-density restriction).
* `ψ_param_unb g_P h_orth ψ` — the **true** submodel functional, fed directly
  into the per-direction-shift sibling of Theorem 8.11 with no affine detour.
* `canonicalPath g` — the fixed internal path realiser, with the measure
  alignment `canonicalPath_curve_eq_unbounded_withDensity` identifying the
  submodel measure with the canonical-path curve.
* `LHS_canonical` — the right-hand side, centered on the true functional
  `ψ((canonicalPath g).curve (1/√n))`.

Because the true functional's coord-0 value at `(1/√n)·h` is exactly
`ψ((canonicalPath (∑ⱼ hⱼ gⱼ)).curve (1/√n))` (`ψ_param_unb_coord_zero_smul`),
the per-`n` inclusion is **exact**: there is no affine centering and hence no
external recenter step.

Reference: van der Vaart, *Asymptotic Statistics*, §25.3.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped InnerProductSpace ENNReal NNReal

namespace AsymptoticStatistics.LowerBounds.LAMUnboundedBridge

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.TangentAbstract
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.QMDPath
open AsymptoticStatistics.ParametricFamily
open AsymptoticStatistics.LowerBounds.RegularEstimator
open AsymptoticStatistics.LowerBounds.LAMSemiparametricBridge
  (T_param_of L_param_of)
open AsymptoticStatistics.LowerBounds.ConvolutionUnbounded
  (ψDot_proj_clm ψDot_proj_clm_coord_zero_eq_inner continuous_single_zero)
open AsymptoticStatistics

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **1-D WithLp/smul/sub computation.** Unfolds the `Fin 1`
`WithLp.equiv`-image of `r • (single a - single b)` at coordinate `0` to
`r * (a - b)`. -/
private lemma withLp_1d_smul_sub_apply (r : ℝ) (a b : ℝ) :
    (WithLp.equiv 2 (Fin 1 → ℝ))
        (r • ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => a)
            - (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => b))) 0
      = r * (a - b) := by
  change WithLp.ofLp (r • (WithLp.toLp 2 (fun _ : Fin 1 => a)
      - WithLp.toLp 2 (fun _ : Fin 1 => b))) 0 = r * (a - b)
  rw [WithLp.ofLp_smul, WithLp.ofLp_sub, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
  simp [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

/-! ## (A) Product measure at `θ = 0` collapses to `P^⊗n`. -/

/-- **Product measure at zero.** The `unboundedParamSubmodel` `n`-fold product
measure at parameter `0` is the i.i.d. `P^⊗n`, since the density at `0` is
identically `1` (`unboundedParamSubmodel_density_zero_eq_one`). -/
theorem productMeasure_unbounded_at_zero {m : ℕ}
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P))) (n : ℕ) :
    AsymptoticRepresentation.productMeasure (unboundedParamSubmodel g_P h_orth) P
        (0 : EuclideanSpace ℝ (Fin m)) n
      = Measure.pi (fun _ : Fin n => P) := by
  unfold AsymptoticRepresentation.productMeasure
  congr 1
  funext _
  -- `P.withDensity (ofReal ∘ density 0) = P` since `density 0 = 1`.
  have h_fun_eq :
      (fun x => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density 0 x))
        = (1 : Ω → ℝ≥0∞) := by
    funext x
    rw [unboundedParamSubmodel_density_zero_eq_one g_P h_orth x, ENNReal.ofReal_one]
    rfl
  rw [h_fun_eq, MeasureTheory.withDensity_one]

/-! ## (B) The true submodel functional and the LHS inclusion. -/

/-- **The true submodel functional** `ψ_param_unb θ := ψ(P.withDensity(ofReal ∘
density θ))`, packaged into `EuclideanSpace ℝ (Fin 1)`. This is the genuine
composition of the statistical functional `ψ` with the `unboundedParamSubmodel`
measure at parameter `θ`, fed directly into the per-direction-shift sibling of
Theorem 8.11. At `θ = 0` it equals `single 0 (ψ P)` (density `0 = 1`); at
`θ = t • h` its coord-0 equals `ψ((canonicalPath (∑ⱼ hⱼ gⱼ)).curve t)` via the
measure alignment `canonicalPath_curve_eq_unbounded_withDensity`. -/
noncomputable def ψ_param_unb
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin 1) :=
  fun θ => (WithLp.equiv 2 _).symm
    (fun _ : Fin 1 => ψ (P.withDensity
      (fun x => ENNReal.ofReal ((unboundedParamSubmodel g_P h_orth).density θ x))))

/-- `ψ_param_unb 0 = single 0 (ψ P)`: the density at `0` is identically `1`, so
`P.withDensity (ofReal ∘ density 0) = P`. -/
lemma ψ_param_unb_at_zero
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) :
    ψ_param_unb g_P h_orth ψ 0
      = EuclideanSpace.single (0 : Fin 1) (ψ P) := by
  have h_withDens :
      P.withDensity (fun x => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density 0 x)) = P := by
    have h_fun_eq :
        (fun x => ENNReal.ofReal
            ((unboundedParamSubmodel g_P h_orth).density 0 x))
          = (1 : Ω → ℝ≥0∞) := by
      funext x
      rw [unboundedParamSubmodel_density_zero_eq_one g_P h_orth x, ENNReal.ofReal_one]
      rfl
    rw [h_fun_eq, MeasureTheory.withDensity_one]
  unfold ψ_param_unb
  rw [h_withDens]
  ext i
  have hi : i = (0 : Fin 1) := Fin.eq_zero i
  subst hi
  change (WithLp.toLp 2 (fun _ : Fin 1 => ψ P)).ofLp 0
    = (EuclideanSpace.single (0 : Fin 1) (ψ P)).ofLp 0
  rw [WithLp.ofLp_toLp, PiLp.single_apply]
  simp

/-- Coord-0 of `ψ_param_unb (t • h)` equals `ψ((canonicalPath (∑ⱼ hⱼ gⱼ)).curve t)`,
the true functional evaluated along the canonical path. Pure rewriting via the
measure alignment `canonicalPath_curve_eq_unbounded_withDensity`. -/
lemma ψ_param_unb_coord_zero_smul
    {m : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → ℝ) (t : ℝ) (h : EuclideanSpace ℝ (Fin m)) :
    (ψ_param_unb g_P h_orth ψ (t • h)).ofLp 0
      = ψ ((canonicalPath
            (∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j)).curve t) := by
  change (WithLp.toLp 2 (fun _ : Fin 1 =>
      ψ (P.withDensity (fun x => ENNReal.ofReal
        ((unboundedParamSubmodel g_P h_orth).density (t • h) x))))).ofLp 0
    = ψ ((canonicalPath
          (∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j)).curve t)
  rw [WithLp.ofLp_toLp,
    canonicalPath_curve_eq_unbounded_withDensity g_P h_orth h t]

/-- **The per-direction functional shift.** For each `h : ℝ^m`, the rescaled
increment of the true functional `ψ_param_unb` converges to `ψDot_proj_clm h`:
`√n · (ψ_param_unb((√n)⁻¹•h) − ψ_param_unb 0) → ψDot_proj_clm h`.

This is exactly the per-direction-shift hypothesis of the Theorem 8.11 sibling.
The proof uses the pathwise difference-quotient mechanism directly: the coord-0
increment equals `(ψ(curve (√n)⁻¹) − ψ P)/(√n)⁻¹`, which converges to the
pathwise derivative `derivative ⟨g, _⟩ = ⟪IF_eff, g⟫` (the EIF identity) along
the null sequence `(√n)⁻¹ → 0`, where `g = ∑ⱼ hⱼ gⱼ = linPerturbScore g_P h`.
No Fréchet or uniform modulus is used: only the per-path Gateaux limit
`derivative_spec`. -/
theorem ψ_param_unb_pointwise_shift
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_linspan : ∀ θ : EuclideanSpace ℝ (Fin m),
      (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {ψ : Measure Ω → ℝ}
    (hψ : PathwiseDifferentiableAt P (tangentSpace T_set) ψ)
    {IF_eff : ↥(L2ZeroMean P)}
    (hEIF : IsEfficientInfluenceFunction P (tangentSpace T_set) hψ.derivative IF_eff)
    (h : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto (fun n : ℕ =>
        (Real.sqrt n) • (ψ_param_unb g_P h_orth ψ ((0 : EuclideanSpace ℝ (Fin m))
            + (Real.sqrt n)⁻¹ • h) - ψ_param_unb g_P h_orth ψ 0))
      Filter.atTop (𝓝 (ψDot_proj_clm g_P IF_eff h)) := by
  classical
  -- The canonical direction `g := ∑ⱼ hⱼ gⱼ = linPerturbScore g_P h ∈ carrier`.
  set g : ↥(L2ZeroMean P) :=
    ∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j with hg_def
  have hg_car : g ∈ T_set.carrier := h_linspan h
  have hg_in : g ∈ tangentSpace T_set :=
    (Submodule.span ℝ T_set.carrier).le_topologicalClosure
      (Submodule.subset_span hg_car)
  -- Score of `canonicalPath g` is `g`; its tangency transports.
  have hscore : (canonicalPath g).score = g := canonicalPath_score g
  have h_in_T : ((canonicalPath g).score : ↥(L2ZeroMean P)) ∈ tangentSpace T_set := by
    rw [hscore]; exact hg_in
  -- Pathwise difference-quotient limit along `𝓝[≠] 0`.
  have h_dq :
      Tendsto
        (fun t : ℝ => (ψ ((canonicalPath g).curve t) - ψ P) / t)
        (nhdsWithin 0 ({0}ᶜ))
        (nhds (hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩)) :=
    hψ.derivative_spec (canonicalPath g) h_in_T
  -- Identify the derivative value with `⟪IF_eff, g⟫` via the EIF identity.
  have h_deriv_eq :
      hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩
        = ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ := by
    have h_if := hEIF.1 ⟨(canonicalPath g).score, h_in_T⟩
    rw [← h_if]; simp only [hscore]
  rw [h_deriv_eq] at h_dq
  -- The null sequence `n ↦ (√n)⁻¹ → 0`, landing in `{0}ᶜ` eventually.
  have h_sqn_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_inv_to_zero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    h_sqn_atTop.inv_tendsto_atTop
  have h_sqn_ne : ∀ᶠ n : ℕ in atTop, Real.sqrt n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)).ne'
  have h_inv_in_compl : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [h_sqn_ne] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact inv_ne_zero hn
  have h_inv_to_zero' :
      Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhdsWithin 0 ({0}ᶜ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_inv_to_zero h_inv_in_compl
  -- The difference quotient along `(√n)⁻¹` converges to `⟪IF_eff, g⟫`.
  have h_dq_seq :
      Tendsto
        (fun n : ℕ =>
          (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P) / (Real.sqrt n)⁻¹)
        atTop (nhds (⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ)) :=
    h_dq.comp h_inv_to_zero'
  -- The target sequence coincides (coord-0) with the difference quotient.
  -- It suffices to prove the limit at the scalar level then lift to `Fin 1`.
  have h_coord_limit :
      Tendsto (fun n : ℕ => Real.sqrt n *
          (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P))
        atTop (nhds (⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ)) := by
    refine h_dq_seq.congr' ?_
    filter_upwards [h_sqn_ne] with n hn
    field_simp
  -- Lift to `EuclideanSpace ℝ (Fin 1)` via the `WithLp.equiv` homeomorphism.
  -- The target vector sequence is `single 0 (√n · (ψ(curve) − ψ P))`, which
  -- converges to `single 0 ⟪IF_eff, g⟫ = ψDot_proj_clm h`.
  have h_eq_vec : ∀ n : ℕ,
      (Real.sqrt n) • (ψ_param_unb g_P h_orth ψ ((0 : EuclideanSpace ℝ (Fin m))
            + (Real.sqrt n)⁻¹ • h) - ψ_param_unb g_P h_orth ψ 0)
        = EuclideanSpace.single (0 : Fin 1)
            (Real.sqrt n * (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P)) := by
    intro n
    rw [zero_add]
    ext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [PiLp.smul_apply, PiLp.sub_apply]
    rw [ψ_param_unb_coord_zero_smul g_P h_orth ψ (Real.sqrt n)⁻¹ h,
      ψ_param_unb_at_zero g_P h_orth ψ]
    rw [PiLp.single_apply, PiLp.single_apply]
    simp only [if_true, smul_eq_mul]
    ring
  -- The derivative value as `single 0 ⟪IF_eff, g⟫`.
  have h_deriv_vec :
      ψDot_proj_clm g_P IF_eff h
        = EuclideanSpace.single (0 : Fin 1) ⟪(IF_eff : ↥(L2ZeroMean P)), g⟫_ℝ := by
    ext i
    have hi : i = (0 : Fin 1) := Fin.eq_zero i
    subst hi
    rw [ψDot_proj_clm_coord_zero_eq_inner g_P IF_eff h, PiLp.single_apply]
    rw [if_pos rfl]
    -- `linPerturbScore g_P h = ∑ⱼ hⱼ gⱼ = g` (definitional).
    rw [show (linPerturbScore g_P h : ↥(L2ZeroMean P)) = g from by rw [hg_def]; rfl]
  rw [h_deriv_vec]
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => (h_eq_vec n).symm)) ?_
  exact (continuous_single_zero.tendsto _).comp h_coord_limit

/-- **The LHS inclusion.** The `localAsymptoticRisk` over the
`unboundedParamSubmodel` with the **true submodel functional** `ψ_param_unb`
(lifted via `T_param_of`, `L_param_of`) is bounded above by `LHS_canonical`
directly, with no affine surrogate and no external recenter. Every `h ∈ ℝ^m`
corresponds to `∑ⱼ hⱼ gⱼ ∈ T_set.carrier` (the linear-span case), so the
parametric supremum over finite `I ⊂ ℝ^m` is a sub-supremum of the
`LHS_canonical` supremum over `I ⊂ T_set.carrier`. Because the true functional's
coord-0 at `(√n)⁻¹•h` is exactly `ψ((canonicalPath g).curve (√n)⁻¹)` (the
`LHS_canonical` centering), via `canonicalPath_curve_eq_unbounded_withDensity`
the per-`n` inclusion is **exact**: no recenter step. -/
theorem unboundedLam_le_LHS_canonical
    {m : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (_h_basis_in : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (h_linspan : ∀ θ : EuclideanSpace ℝ (Fin m),
      (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (T_n : ∀ n, (Fin n → Ω) → ℝ) (_hT_n : ∀ n, Measurable (T_n n))
    (ψ : Measure Ω → ℝ) (ℓ_M : ℝ → ℝ≥0∞) :
    LocalAsymptoticMinimax.localAsymptoticRisk
        (unboundedParamSubmodel g_P h_orth) P (0 : EuclideanSpace ℝ (Fin m))
        (T_param_of T_n)
        (ψ_param_unb g_P h_orth ψ)
        (L_param_of ℓ_M)
      ≤ LHS_canonical T_set T_n ψ ℓ_M := by
  classical
  unfold LocalAsymptoticMinimax.localAsymptoticRisk LHS_canonical
  refine iSup_le ?_
  intro I_param
  -- The `LHS_canonical` image of `I_param` under `h ↦ ∑ⱼ hⱼ gⱼ`.
  let I_semip_set : Finset ↥(L2ZeroMean P) :=
    I_param.image (fun h : EuclideanSpace ℝ (Fin m) =>
      ∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j)
  have hI_semip_subset :
      (↑I_semip_set : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro g hg_mem
    rcases Finset.mem_image.mp hg_mem with ⟨h_param, _, rfl⟩
    exact h_linspan h_param
  refine le_iSup_of_le ⟨I_semip_set, hI_semip_subset⟩ ?_
  -- liminf-mono: per-n bound suffices.
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall ?_)
  intro n
  -- Per-n: parametric ⨆ h ∈ I_param ≤ Finset.sup I_semip ...
  refine iSup_le ?_
  intro h_param
  refine iSup_le ?_
  intro h_in_I_param
  -- The corresponding `LHS_canonical` direction `g := ∑ⱼ h_param,ⱼ gⱼ`.
  set g : ↥(L2ZeroMean P) :=
    ∑ j : Fin m, ((WithLp.equiv 2 _) h_param) j • g_P j with hg_def
  have hg_in_I_semip : g ∈ I_semip_set :=
    Finset.mem_image.mpr ⟨h_param, h_in_I_param, hg_def.symm⟩
  -- The `LHS_canonical` Finset.sup target function.
  let f_semip : ↥(L2ZeroMean P) → ℝ≥0∞ := fun g' =>
    ∫⁻ X : Fin n → Ω,
      ℓ_M (Real.sqrt n *
        (T_n n X - ψ ((canonicalPath g').curve ((Real.sqrt n)⁻¹))))
      ∂(MeasureTheory.Measure.pi
          (fun _ : Fin n => (canonicalPath g').curve ((Real.sqrt n)⁻¹)))
  -- Measure equality: `productMeasure unbounded` at `(√n)⁻¹•h` factorwise equals
  -- `Measure.pi (canonicalPath g).curve(√n)⁻¹` via the measure alignment.
  have h_measure_eq :
      AsymptoticRepresentation.productMeasure (unboundedParamSubmodel g_P h_orth) P
          ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param) n
        = MeasureTheory.Measure.pi
            (fun _ : Fin n => (canonicalPath g).curve (Real.sqrt n)⁻¹) := by
    unfold AsymptoticRepresentation.productMeasure
    congr 1
    funext _
    rw [zero_add, hg_def]
    exact (canonicalPath_curve_eq_unbounded_withDensity g_P h_orth h_param
      (Real.sqrt n)⁻¹).symm
  -- Pointwise integrand equality after the measure substitution.
  -- The true functional's coord-0 at `(√n)⁻¹•h_param` is the `LHS_canonical`
  -- centering `ψ((canonicalPath g).curve (√n)⁻¹)`: exact, no recenter.
  have h_integrand_eq : ∀ ω : Fin n → Ω,
      L_param_of ℓ_M
          ((Real.sqrt n) • (T_param_of T_n n ω
            - ψ_param_unb g_P h_orth ψ
                ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param)))
        = ℓ_M (Real.sqrt n *
            (T_n n ω - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)))) := by
    intro ω
    rw [zero_add]
    -- coord-0 of `ψ_param_unb ((√n)⁻¹ • h_param)` = `ψ(curve (√n)⁻¹)`.
    have h_coord :
        (ψ_param_unb g_P h_orth ψ ((Real.sqrt n)⁻¹ • h_param)).ofLp 0
          = ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) := by
      rw [ψ_param_unb_coord_zero_smul g_P h_orth ψ (Real.sqrt n)⁻¹ h_param, hg_def]
    -- Unfold `L_param_of` / `T_param_of` and use the 1-D WithLp helper.
    change ℓ_M ((WithLp.equiv 2 (Fin 1 → ℝ))
                ((Real.sqrt n) • (
                  (WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ : Fin 1 => T_n n ω)
                  - ψ_param_unb g_P h_orth ψ ((Real.sqrt n)⁻¹ • h_param))) 0)
          = ℓ_M (Real.sqrt n * (T_n n ω
              - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))))
    -- Rewrite `ψ_param_unb ((√n)⁻¹ • h_param)` to its coord-0 `single` form.
    rw [show ψ_param_unb g_P h_orth ψ ((Real.sqrt n)⁻¹ • h_param)
          = (WithLp.equiv 2 (Fin 1 → ℝ)).symm
              (fun _ : Fin 1 => ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)))
            from ?_]
    · rw [withLp_1d_smul_sub_apply]
    · apply (WithLp.equiv 2 (Fin 1 → ℝ)).injective
      funext i
      have hi : i = (0 : Fin 1) := Fin.eq_zero i
      subst hi
      rw [Equiv.apply_symm_apply]
      exact h_coord
  -- Combine: rewrite measure + integrand, then bound by Finset.sup of f_semip.
  have h_step1 : ∫⁻ ω, L_param_of ℓ_M
              ((Real.sqrt n) • (T_param_of T_n n ω
                - ψ_param_unb g_P h_orth ψ
                    ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param)))
              ∂(AsymptoticRepresentation.productMeasure (unboundedParamSubmodel g_P h_orth) P
                  ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param) n)
      = f_semip g := by
    rw [h_measure_eq]
    exact lintegral_congr h_integrand_eq
  rw [h_step1]
  exact Finset.le_sup (f := f_semip) hg_in_I_semip

/-! ## (C) Vector-valued (codomain `EuclideanSpace ℝ (Fin d)`) siblings.

Vector-direct versions of §(B) for the `k`-dimensional codomain. The estimator
`T_n` and functional `ψ` are `EuclideanSpace ℝ (Fin d)`-valued; the true submodel
functional `ψ_param_unb_vec` returns `ψ(measure)` directly (no `single 0` lift),
the per-direction shift converges to `ψDot_proj_vec_clm` (from
`ConvolutionUnboundedVec`), and the LHS inclusion lands in `LHS_canonical_vec`. The
existing `ψDotMat_vec` / `ψDot_proj_vec_clm` / `T_param_of_vec` are reused. -/

open AsymptoticStatistics.LowerBounds.ConvolutionUnboundedVec
  (ψDot_proj_vec_clm ψDot_proj_vec_clm_coord_eq_inner T_param_of_vec)

/-- **The true submodel functional (vector codomain).** Returns `ψ(measure)`
directly into `EuclideanSpace ℝ (Fin d)` (no `single 0` lift). At `θ = 0` it equals
`ψ P` (density `0 = 1`). -/
noncomputable def ψ_param_unb_vec {m d : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d) :=
  fun θ => ψ (P.withDensity
    (fun x => ENNReal.ofReal ((unboundedParamSubmodel g_P h_orth).density θ x)))

/-- `ψ_param_unb_vec 0 = ψ P`: the density at `0` is identically `1`, so
`P.withDensity (ofReal ∘ density 0) = P`. No `single` lift needed (codomain is general). -/
lemma ψ_param_unb_at_zero_vec {m d : ℕ} (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d)) :
    ψ_param_unb_vec g_P h_orth ψ 0 = ψ P := by
  have h_withDens :
      P.withDensity (fun x => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density 0 x)) = P := by
    have h_fun_eq :
        (fun x => ENNReal.ofReal
            ((unboundedParamSubmodel g_P h_orth).density 0 x))
          = (1 : Ω → ℝ≥0∞) := by
      funext x
      rw [unboundedParamSubmodel_density_zero_eq_one g_P h_orth x, ENNReal.ofReal_one]
      rfl
    rw [h_fun_eq, MeasureTheory.withDensity_one]
  unfold ψ_param_unb_vec
  rw [h_withDens]

/-- **The per-direction functional shift (vector codomain).** For each
`h : ℝ^m`, the rescaled increment of the true functional `ψ_param_unb_vec`
converges to `ψDot_proj_vec_clm g_P IF_eff h`:
`√n • (ψ_param_unb_vec((√n)⁻¹•h) − ψ_param_unb_vec 0) → ψDot_proj_vec_clm h`.

The proof uses the vector pathwise difference-quotient mechanism directly: the
increment equals `(√n)⁻¹⁻¹ • (ψ(curve (√n)⁻¹) − ψ P)`, converging to the pathwise
derivative `derivative ⟨g, _⟩` along `(√n)⁻¹ → 0`, where `g = ∑ⱼ hⱼ gⱼ`. The
derivative value coincides with `ψDot_proj_vec_clm h` coordinatewise via the EIF
identity (`hEIF j` + `ψDot_proj_vec_clm_coord_eq_inner`). -/
theorem ψ_param_unb_pointwise_shift_vec {m d : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (h_linspan : ∀ θ : EuclideanSpace ℝ (Fin m),
      (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    {ψ : Measure Ω → EuclideanSpace ℝ (Fin d)}
    (hψ : Core.PathwiseVec.PathwiseDifferentiableAt_vec P
      (Core.TangentAbstract.tangentSpace T_set) ψ)
    {IF_eff : Fin d → ↥(L2ZeroMean P)}
    (hEIF : Core.EIFVec.IsEfficientInfluenceFunction_vec hψ.derivative IF_eff)
    (h : EuclideanSpace ℝ (Fin m)) :
    Filter.Tendsto (fun n : ℕ => (Real.sqrt n) •
        (ψ_param_unb_vec g_P h_orth ψ ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h)
          - ψ_param_unb_vec g_P h_orth ψ 0))
      Filter.atTop (𝓝 (ψDot_proj_vec_clm g_P IF_eff h)) := by
  classical
  -- The canonical direction `g := ∑ⱼ hⱼ gⱼ = linPerturbScore g_P h ∈ carrier`.
  set g : ↥(L2ZeroMean P) :=
    ∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j with hg_def
  have hg_car : g ∈ T_set.carrier := h_linspan h
  have hg_in : g ∈ Core.TangentAbstract.tangentSpace T_set :=
    (Submodule.span ℝ T_set.carrier).le_topologicalClosure
      (Submodule.subset_span hg_car)
  -- Score of `canonicalPath g` is `g`; its tangency transports.
  have hscore : (canonicalPath g).score = g := canonicalPath_score g
  have h_in_T : ((canonicalPath g).score : ↥(L2ZeroMean P))
      ∈ Core.TangentAbstract.tangentSpace T_set := by
    rw [hscore]; exact hg_in
  -- Vector pathwise difference-quotient limit along `𝓝[≠] 0`.
  have h_dq :
      Tendsto
        (fun t : ℝ => t⁻¹ • (ψ ((canonicalPath g).curve t) - ψ P))
        (nhdsWithin 0 ({0}ᶜ))
        (nhds (hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩)) :=
    hψ.derivative_spec (canonicalPath g) h_in_T
  -- The null sequence `n ↦ (√n)⁻¹ → 0`, landing in `{0}ᶜ` eventually.
  have h_sqn_atTop : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have h_inv_to_zero : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    h_sqn_atTop.inv_tendsto_atTop
  have h_sqn_ne : ∀ᶠ n : ℕ in atTop, Real.sqrt n ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    exact (Real.sqrt_pos.mpr (lt_of_lt_of_le one_pos hn1)).ne'
  have h_inv_in_compl : ∀ᶠ n : ℕ in atTop, (Real.sqrt n)⁻¹ ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [h_sqn_ne] with n hn
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact inv_ne_zero hn
  have h_inv_to_zero' :
      Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (nhdsWithin 0 ({0}ᶜ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_inv_to_zero h_inv_in_compl
  -- The difference quotient along `(√n)⁻¹` converges to `derivative ⟨g, _⟩`.
  have h_dq_seq :
      Tendsto
        (fun n : ℕ =>
          ((Real.sqrt n)⁻¹)⁻¹ • (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P))
        atTop (nhds (hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩)) :=
    h_dq.comp h_inv_to_zero'
  -- Convert `((√n)⁻¹)⁻¹ • _` to `√n • _` eventually (n ≥ 1).
  have h_coord_limit :
      Tendsto (fun n : ℕ => Real.sqrt n •
          (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P))
        atTop (nhds (hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩)) := by
    refine h_dq_seq.congr' ?_
    filter_upwards [h_sqn_ne] with n hn
    rw [inv_inv]
  -- Identify `derivative ⟨g, _⟩ = ψDot_proj_vec_clm g_P IF_eff h` coordinatewise.
  have h_deriv_eq :
      hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩
        = ψDot_proj_vec_clm g_P IF_eff h := by
    ext j
    -- LHS coord j via EIF for `EuclideanSpace.proj j ∘L derivative`.
    have hEIF_j := hEIF j
    have hIF_j := hEIF_j.1
    have h_coord_lhs :
        (hψ.derivative ⟨(canonicalPath g).score, h_in_T⟩).ofLp j
          = ⟪(IF_eff j : ↥(L2ZeroMean P)), g⟫_ℝ := by
      have hg_eq : (⟨(canonicalPath g).score, h_in_T⟩
            : Core.TangentAbstract.tangentSpace T_set)
            = ⟨(g : ↥(L2ZeroMean P)), hg_in⟩ := by
        apply Subtype.ext; exact hscore
      rw [hg_eq]
      have h_apply := hIF_j ⟨(g : ↥(L2ZeroMean P)), hg_in⟩
      have h_proj_eq :
          (EuclideanSpace.proj j ∘L hψ.derivative) ⟨(g : ↥(L2ZeroMean P)), hg_in⟩
            = (hψ.derivative ⟨(g : ↥(L2ZeroMean P)), hg_in⟩).ofLp j := rfl
      rw [h_proj_eq] at h_apply
      exact h_apply.symm
    -- RHS coord j: ψDot_proj_vec_clm h)_j = ⟪IF_eff j, linPerturbScore g_P h⟫ = ⟪IF_eff j, g⟫.
    have h_coord_rhs :
        (ψDot_proj_vec_clm g_P IF_eff h).ofLp j
          = ⟪(IF_eff j : ↥(L2ZeroMean P)), g⟫_ℝ := by
      rw [ψDot_proj_vec_clm_coord_eq_inner g_P IF_eff h j]
      congr 1
    rw [h_coord_lhs, h_coord_rhs]
  rw [h_deriv_eq] at h_coord_limit
  -- The target sequence equals `√n • (ψ(curve) − ψ P)` eventually, via measure alignment.
  have h_eq_vec : ∀ n : ℕ,
      (Real.sqrt n) • (ψ_param_unb_vec g_P h_orth ψ ((0 : EuclideanSpace ℝ (Fin m))
            + (Real.sqrt n)⁻¹ • h) - ψ_param_unb_vec g_P h_orth ψ 0)
        = Real.sqrt n • (ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) - ψ P) := by
    intro n
    rw [zero_add]
    congr 2
    · -- ψ_param_unb_vec ((√n)⁻¹ • h) = ψ(curve (√n)⁻¹)
      change ψ (P.withDensity (fun x => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density ((Real.sqrt n)⁻¹ • h) x)))
        = ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))
      rw [hg_def,
        canonicalPath_curve_eq_unbounded_withDensity g_P h_orth h (Real.sqrt n)⁻¹]
    · -- ψ_param_unb_vec 0 = ψ P
      exact ψ_param_unb_at_zero_vec g_P h_orth ψ
  refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun n => (h_eq_vec n).symm)) ?_
  exact h_coord_limit

/-- **The LHS inclusion (vector codomain).** The `localAsymptoticRisk`
over the `unboundedParamSubmodel` with the **true submodel functional**
`ψ_param_unb_vec` (lifted via `T_param_of_vec`, with the vector loss `ℓ_M` used
directly) is bounded above by `LHS_canonical_vec`. The `iSup`/`liminf`/`Finset.sup`
plumbing is codomain-independent; the per-`n` inclusion is **exact** via the same
`canonicalPath_curve_eq_unbounded_withDensity` alignment, now vector-direct. -/
theorem unboundedLam_le_LHS_canonical_vec {m d : ℕ} (T_set : TangentSpec P)
    (g_P : Fin m → ↥(L2ZeroMean P))
    (h_orth : Orthonormal ℝ (fun i : Fin m => (g_P i : Lp ℝ 2 P)))
    (_h_basis_in : ∀ j, (g_P j : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (h_linspan : ∀ θ : EuclideanSpace ℝ (Fin m),
      (∑ j, ((WithLp.equiv 2 _) θ) j • (g_P j) : ↥(L2ZeroMean P)) ∈ T_set.carrier)
    (T_n : ∀ n, (Fin n → Ω) → EuclideanSpace ℝ (Fin d)) (_hT_n : ∀ n, Measurable (T_n n))
    (ψ : Measure Ω → EuclideanSpace ℝ (Fin d))
    (ℓ_M : EuclideanSpace ℝ (Fin d) → ℝ≥0∞) :
    LocalAsymptoticMinimax.localAsymptoticRisk
        (unboundedParamSubmodel g_P h_orth) P (0 : EuclideanSpace ℝ (Fin m))
        (T_param_of_vec T_n)
        (ψ_param_unb_vec g_P h_orth ψ)
        ℓ_M
      ≤ LHS_canonical_vec T_set T_n ψ ℓ_M := by
  classical
  unfold LocalAsymptoticMinimax.localAsymptoticRisk LHS_canonical_vec
  refine iSup_le ?_
  intro I_param
  -- The `LHS_canonical_vec` image of `I_param` under `h ↦ ∑ⱼ hⱼ gⱼ`.
  let I_semip_set : Finset ↥(L2ZeroMean P) :=
    I_param.image (fun h : EuclideanSpace ℝ (Fin m) =>
      ∑ j : Fin m, ((WithLp.equiv 2 _) h) j • g_P j)
  have hI_semip_subset :
      (↑I_semip_set : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro g hg_mem
    rcases Finset.mem_image.mp hg_mem with ⟨h_param, _, rfl⟩
    exact h_linspan h_param
  refine le_iSup_of_le ⟨I_semip_set, hI_semip_subset⟩ ?_
  -- liminf-mono: per-n bound suffices.
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall ?_)
  intro n
  -- Per-n: parametric ⨆ h ∈ I_param ≤ Finset.sup I_semip ...
  refine iSup_le ?_
  intro h_param
  refine iSup_le ?_
  intro h_in_I_param
  -- The corresponding `LHS_canonical_vec` direction `g := ∑ⱼ h_param,ⱼ gⱼ`.
  set g : ↥(L2ZeroMean P) :=
    ∑ j : Fin m, ((WithLp.equiv 2 _) h_param) j • g_P j with hg_def
  have hg_in_I_semip : g ∈ I_semip_set :=
    Finset.mem_image.mpr ⟨h_param, h_in_I_param, hg_def.symm⟩
  -- The `LHS_canonical_vec` Finset.sup target function.
  let f_semip : ↥(L2ZeroMean P) → ℝ≥0∞ := fun g' =>
    ∫⁻ X : Fin n → Ω,
      ℓ_M (Real.sqrt n •
        (T_n n X - ψ ((canonicalPath g').curve ((Real.sqrt n)⁻¹))))
      ∂(MeasureTheory.Measure.pi
          (fun _ : Fin n => (canonicalPath g').curve ((Real.sqrt n)⁻¹)))
  -- Measure equality via the measure alignment.
  have h_measure_eq :
      AsymptoticRepresentation.productMeasure (unboundedParamSubmodel g_P h_orth) P
          ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param) n
        = MeasureTheory.Measure.pi
            (fun _ : Fin n => (canonicalPath g).curve (Real.sqrt n)⁻¹) := by
    unfold AsymptoticRepresentation.productMeasure
    congr 1
    funext _
    rw [zero_add, hg_def]
    exact (canonicalPath_curve_eq_unbounded_withDensity g_P h_orth h_param
      (Real.sqrt n)⁻¹).symm
  -- Pointwise integrand equality after the measure substitution. The true
  -- functional at `(√n)⁻¹•h_param` is the `LHS_canonical_vec` centering: exact.
  have h_integrand_eq : ∀ ω : Fin n → Ω,
      ℓ_M ((Real.sqrt n) • (T_param_of_vec T_n n ω
            - ψ_param_unb_vec g_P h_orth ψ
                ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param)))
        = ℓ_M (Real.sqrt n •
            (T_n n ω - ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)))) := by
    intro ω
    rw [zero_add]
    -- ψ_param_unb_vec ((√n)⁻¹ • h_param) = ψ(curve (√n)⁻¹) (measure alignment), and
    -- `T_param_of_vec T_n = T_n` definitionally — rewrite both sides of the subtraction.
    have hψ_eq : ψ_param_unb_vec g_P h_orth ψ ((Real.sqrt n)⁻¹ • h_param)
        = ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹)) := by
      change ψ (P.withDensity (fun x => ENNReal.ofReal
          ((unboundedParamSubmodel g_P h_orth).density ((Real.sqrt n)⁻¹ • h_param) x)))
        = ψ ((canonicalPath g).curve ((Real.sqrt n)⁻¹))
      rw [hg_def,
        canonicalPath_curve_eq_unbounded_withDensity g_P h_orth h_param (Real.sqrt n)⁻¹]
    rw [show T_param_of_vec T_n n ω = T_n n ω from rfl, hψ_eq]
  -- Combine: rewrite measure + integrand, then bound by Finset.sup of f_semip.
  have h_step1 : ∫⁻ ω, ℓ_M
              ((Real.sqrt n) • (T_param_of_vec T_n n ω
                - ψ_param_unb_vec g_P h_orth ψ
                    ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param)))
              ∂(AsymptoticRepresentation.productMeasure (unboundedParamSubmodel g_P h_orth) P
                  ((0 : EuclideanSpace ℝ (Fin m)) + (Real.sqrt n)⁻¹ • h_param) n)
      = f_semip g := by
    rw [h_measure_eq]
    exact lintegral_congr h_integrand_eq
  rw [h_step1]
  exact Finset.le_sup (f := f_semip) hg_in_I_semip

end AsymptoticStatistics.LowerBounds.LAMUnboundedBridge
