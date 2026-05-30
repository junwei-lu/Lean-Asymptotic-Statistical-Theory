# Asymptotic Statistics in Lean 4: A Source-Faithful Formalization of Parametric and Semiparametric Efficiency Theory

<p align="center">
  <a href="#"><img src="https://img.shields.io/badge/Lean-4-blueviolet?style=for-the-badge" alt="Lean 4"></a>
  <a href="#"><img src="https://img.shields.io/badge/Mathlib-v4.29.1-brightgreen?style=for-the-badge" alt="Mathlib"></a>

## Abstract

We present a systematic Lean 4 formalization of asymptotic statistical
estimation theory.  
The development was produced under a hypothesis-disciplined
multi-agent workflow.

## Installation Guide 

### 1. Make sure you have [installed Lean](https://leanprover-community.github.io/get_started.html). We suggest installing `elan`.

`elan` is the analogue of `rustup` for Lean 4.  It manages multiple
Lean versions side-by-side and reads the `lean-toolchain` file in this
repository to pick the exact version we use.

**macOS / Linux / WSL:**

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
source $HOME/.elan/env   # add this line to ~/.zshrc or ~/.bashrc
```

**Windows (PowerShell):**

```powershell
curl -L https://github.com/leanprover/elan/releases/latest/download/elan-init.ps1 -o elan-init.ps1
.\elan-init.ps1
```

Verify the install:

```bash
elan --version
lean --version    # may say "no toolchain" until step 3 — that is fine
lake --version    # lake ships with Lean and is installed by elan
```

### 2. Clone the repository

```bash
git clone https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory.git
cd Lean-Asymptotic-Statistical-Theory
```

The `lean-toolchain` file in this directory pins the exact Lean 4
version compatible with Mathlib `v4.29.1` (see `lakefile.lean`).
`elan` will auto-install it on the next `lake` invocation.

### 3. Fetch the Mathlib build cache

Mathlib is large; building it from scratch takes hours.  The Mathlib
maintainers publish a precompiled cache that `lake exe cache get`
downloads in a few minutes:

```bash
lake exe cache get
```

### 4. Build the library

```bash
lake build
```

### 5. Use the library as a dependency 

To pull this library into your own Lean project, add the following to
your `lakefile.lean`:

```lean
require AsymptoticStatistics from git
  "https://github.com/junwei-lu/Lean-Asymptotic-Statistical-Theory.git" @ "main"
```

then run `lake update && lake exe cache get && lake build`.  Your
project must use the same Lean toolchain version pinned in this
repository's `lean-toolchain` file.

## Formalization Results

We formalize the following results from van der Vaart (1998),
*Asymptotic Statistics*.

### Core definitions

The concept layer that downstream theorems quantify over.

| Name | File | Reference |
|------|------|-----------|
| `DifferentiableQuadraticMean` | `DQM/Defs.lean` | vdV (1998), Eq (7.1) — DQM |
| `QMDPath` | `Core/QMDPath.lean` | vdV (1998), §7.2 — quadratic-mean-differentiable path |
| `RegularEstimatorSequence` | `ParametricFamily/RegularEstimator.lean` | vdV (1998), §8.5 — regular estimator sequence |
| `IsRegularEstimator` | `LowerBounds/RegularEstimator.lean` | vdV (1998), §25.3 — regular estimator (semiparametric) |
| `BowlShaped` | `ForMathlib/BowlShaped.lean` | vdV (1998), §8.7 — bowl-shaped loss function |
| `TangentSpec` | `Core/TangentAbstract.lean` | vdV (1998), §25.3 — tangent set / tangent space |
| `IsGaussianShift` | `Experiment/GaussianShift.lean` | vdV (1998), §8.2 — Gaussian shift experiment |
| `IsEquivariantInLaw` | `Experiment/EquivariantInLaw.lean` | vdV (1998), §8.4 — equivariant-in-law estimator |
| `IsPGlivenkoCantelli` | `EmpiricalProcess/GlivenkoCantelli.lean` | vdV (1998), §19.1 — Glivenko–Cantelli class |
| `IsPDonsker` | `EmpiricalProcess/Donsker.lean` | vdV (1998), §19.2 — Donsker class |
| `IsBracket` / `IsEpsBracket` | `EmpiricalProcess/Bracketing.lean` | vdV (1998), §19.2 — ε-bracket |
| `HasFiniteBracketingCover` | `EmpiricalProcess/Bracketing.lean` | vdV (1998), §19.2 — bracketing number `N_[](ε, F, L_r)` |
| `IsEnvelope` | `EmpiricalProcess/FunctionClass.lean` | vdV (1998), §19.2 — envelope function |
| `IsCoarseningAtRandom` | `Operators/CAR.lean` | vdV (1998), §25.6 — coarsening at random |

### Local Asymptotic Normality

| Name | File | Reference |
|------|------|-----------|
| `paramSubmodel_DQM` | `ParametricFamily/SubmodelDQM.lean` | vdV (1998), Eq (7.1) |
| `LAN_expansion` | `LocalAsymptoticNormality/LANExpansion.lean` | vdV (1998), Thm 7.2 |

### Parametric Efficiency

| Name | File | Reference |
|------|------|-----------|
| `contiguous_local_alternatives` | `LocalAsymptoticNormality/AsymptoticRepresentation.lean` | vdV (1998), Thm 6.5 |
| `regularity_implies_8_2_hypothesis` | `Efficiency/HajekLeCamConvolution.lean` | vdV (1998), Thm 8.2 |
| `LAN_representation_vdV` | `LocalAsymptoticNormality/AsymptoticRepresentation.lean` | vdV (1998), Thm 8.4 |
| `anderson_lemma_set` | `ForMathlib/Anderson.lean` | vdV (1998), Lem 8.5 (Anderson 1955) |
| `hajek_le_cam_convolution_theorem` | `Efficiency/HajekLeCamConvolution.lean` | vdV (1998), Thm 8.8 |
| `local_asymptotic_minimax_bound` | `Efficiency/LocalAsymptoticMinimax.lean` | vdV (1998), Thm 8.11 |

### Empirical processes

| Name | File | Reference |
|------|------|-----------|
| `isPGlivenkoCantelli_of_finite_bracketing_L1` | `EmpiricalProcess/GlivenkoCantelli.lean` | vdV (1998), Thm 19.4 |
| `isPDonsker_of_finite_bracketing_entropy_integral` | `EmpiricalProcess/DonskerBracketing.lean` | vdV (1998), Thm 19.5 |
| `donsker_random_function_consistency` | `EmpiricalProcess/RandomFunctions.lean` | vdV (1998), Lem 19.24 |
| `empiricalProcess_param_estimation` | `EmpiricalProcess/ParameterEstimation.lean` | vdV (1998), Thm 19.26 |
| `bernstein_inequality` | `EmpiricalProcess/Maximal.lean` | vdV (1998), Lem 19.32 |
| `finite_sup_bound` | `EmpiricalProcess/Maximal.lean` | vdV (1998), Lem 19.33 |
| `maximal_inequality_bracketing` | `EmpiricalProcess/Maximal.lean` | vdV (1998), Lem 19.34 |

### Semiparametric models and efficiency

| Name | File | Reference |
|------|------|-----------|
| `score_in_L2ZeroMean` | `Core/QMDPath.lean` | vdV (1998), Lem 25.14 |
| `eif_eq_orthogonalProjection` | `Core/EIF.lean` | vdV (1998), Thm 25.18 |
| `efficient_bound_eq_sup_ratio` | `Core/EIF.lean` | vdV (1998), Lem 25.19 |
| `semiparametric_convolution_theorem` | `LowerBounds/Convolution.lean` | vdV (1998), Thm 25.20 |
| `lam_semiparametric` | `LowerBounds/LAMSemiparametric.lean` | vdV (1998), Thm 25.21 |
| `estimator_semiparametricallyEfficient_of_asympLinear_eif` | `Core/EfficiencyOperational.lean` | vdV (1998), Eq (25.22) |
| `eif_from_efficientScore` | `StrictModel/EfficientScore.lean` | vdV (1998), Lem 25.25 |
| `eif_via_information_operator` | `Operators/ScoreOperator.lean` | vdV (1998), Eq (25.30) |
| `eif_via_adjoint_equation` | `Operators/ScoreOperator.lean` | vdV (1998), Thm 25.31 |
| `efficientScore_projection_formula` | `Operators/ScoreOperator.lean` | vdV (1998), Eq (25.33) |
| `influence_on_sup_of_subtract_proj_nuisance` | `Core/EIF.lean` | vdV (1998), Cor 25.42 |
| `zEstimator_semiparametricallyEfficient` | `Asymptotics/ZEstimator.lean` | vdV (1998), Thm 25.54 |
| `oneStep_semiparametricallyEfficient` | `Asymptotics/OneStep.lean` | vdV (1998), Thm 25.57 |
| `zEstimator_biasResidual_expansion` | `Asymptotics/ZEstimator.lean` | vdV (1998), Thm 25.59 |
| `mle_semiparametricallyEfficient` | `Asymptotics/LeastFavorable.lean` | vdV (1998), Thm 25.77 |

### Foundational results (not yet in Mathlib)

We also formalize the following standard results in probability and
analysis that are used as load-bearing infrastructure by the
asymptotic-statistics layer but are not yet available upstream in
Mathlib `v4.29.1`.  Each row links to the bibliography entry in
[§ References](#references).

| Name | File | Result |
|------|------|--------|
| `prekopaLeindler` | `ForMathlib/PrekopaLeindler.lean` | Prékopa–Leindler inequality on ℝⁿ [\[Prékopa 1973\]](#ref-prekopa1973) |
| `anderson_lemma_independent` | `ForMathlib/Anderson.lean` | Anderson's lemma, independent coordinates [\[Anderson 1955\]](#ref-anderson1955) |
| `mutuallyContiguous_of_asymptotically_log_normal` | `ForMathlib/Contiguity.lean` | Le Cam's first lemma (mutual contiguity from asymptotic log-normality) [\[vdV 1998, §6.4\]](#ref-vdv1998) |
| `weak_limit_under_Q_of_lecam_third` | `ForMathlib/Contiguity.lean` | Le Cam's third lemma (weak limit transport under contiguity) [\[vdV 1998, §6.7\]](#ref-vdv1998) |
| `levyMpass_vec` | `ForMathlib/LevyMpassVec.lean` | Lévy continuity theorem for vector-valued laws [\[Lévy 1925\]](#ref-levy1925) |
| `tendstoInDistribution_multivariate_clt` | `ForMathlib/MultivariateCLT.lean` | Multivariate CLT via characteristic functions [\[Cramér–Wold 1936\]](#ref-cramerwold1936) |
| `cramerWold_weakConverges` | `ForMathlib/CramerWoldWeakConverges.lean` | Cramér–Wold device for weak convergence [\[Cramér–Wold 1936\]](#ref-cramerwold1936) |
| `WeakConverges.slutsky_of_tendstoInMeasure_dist` | `ForMathlib/Slutsky.lean` | Slutsky's theorem [\[Slutsky 1925\]](#ref-slutsky1925) |
| `doobL2Equiv` | `ForMathlib/CondExpL2.lean` | Doob L² isometry: conditional expectation as L²(σ-sub-algebra) ≃ L²(comap) [\[Doob 1953\]](#ref-doob1953) |
| `lpTrimComapToLpMap` | `ForMathlib/CondExpL2.lean` | Doob-style identification `Lᵖ(μ|_𝒢) ≃ Lᵖ(map μ)` [\[Doob 1953\]](#ref-doob1953) |

## References

<a id="ref-vdv1998"></a>
- **[vdV 1998]** van der Vaart, A. W. (1998). *Asymptotic Statistics*.
  Cambridge Series in Statistical and Probabilistic Mathematics, Vol. 3.
  Cambridge University Press.

<a id="ref-anderson1955"></a>
- **[Anderson 1955]** Anderson, T. W. (1955). The integral of a
  symmetric unimodal function over a symmetric convex set and some
  probability inequalities. *Proceedings of the American Mathematical
  Society*, 6(2), 170–176.

<a id="ref-prekopa1973"></a>
- **[Prékopa 1973]** Prékopa, A. (1973). On logarithmic concave
  measures and functions. *Acta Scientiarum Mathematicarum*, 34,
  335–343.

<a id="ref-lecam1972"></a>
- **[Le Cam 1972]** Le Cam, L. (1972). Limits of experiments. In
  *Proceedings of the Sixth Berkeley Symposium on Mathematical
  Statistics and Probability*, Vol. 1, 245–261.

<a id="ref-hajek1970"></a>
- **[Hájek 1970]** Hájek, J. (1970). A characterization of limiting
  distributions of regular estimates. *Zeitschrift für
  Wahrscheinlichkeitstheorie und Verwandte Gebiete*, 14, 323–330.

<a id="ref-levy1925"></a>
- **[Lévy 1925]** Lévy, P. (1925). *Calcul des Probabilités*.
  Gauthier-Villars, Paris.  (Continuity theorem for characteristic
  functions.)

<a id="ref-cramerwold1936"></a>
- **[Cramér–Wold 1936]** Cramér, H., and Wold, H. (1936). Some
  theorems on distribution functions. *Journal of the London
  Mathematical Society*, 11(4), 290–294.

<a id="ref-slutsky1925"></a>
- **[Slutsky 1925]** Slutsky, E. (1925). Über stochastische
  Asymptoten und Grenzwerte. *Metron*, 5(3), 3–89.

<a id="ref-doob1953"></a>
- **[Doob 1953]** Doob, J. L. (1953). *Stochastic Processes*. Wiley.
  (Conditional-expectation L² isometries, §I.7.)
