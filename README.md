# Asymptotic Statistical Theory in Lean 4

<p align="center">
  <a href="#"><img src="https://img.shields.io/badge/Lean-4-blueviolet?style=for-the-badge" alt="Lean 4"></a>
  <a href="#"><img src="https://img.shields.io/badge/Mathlib-v4.29.1-brightgreen?style=for-the-badge" alt="Mathlib"></a>


We present a systematic Lean 4 formalization of asymptotic statistical
estimation theory, especially parametric and semiparametric efficiency theory.
The development was produced under a hypothesis-disciplined
multi-agent workflow using the reference of [van der Vaart (1998)](https://www.cambridge.org/core/books/asymptotic-statistics/A3C7DAD3F7E66A1FA60E9C8FE132EE1D).


- [Asymptotic Statistical Theory in Lean 4](#asymptotic-statistical-theory-in-lean-4)
  - [Installation Guide](#installation-guide)
    - [1. Make sure you have installed Lean. We suggest installing `elan`.](#1-make-sure-you-have-installed-lean-we-suggest-installing-elan)
    - [2. Clone the repository](#2-clone-the-repository)
    - [3. Fetch the Mathlib build cache](#3-fetch-the-mathlib-build-cache)
    - [4. Build the library](#4-build-the-library)
    - [5. Use the library as a dependency](#5-use-the-library-as-a-dependency)
  - [Formalization Results](#formalization-results)
    - [Core definitions](#core-definitions)
    - [Local Asymptotic Normality](#local-asymptotic-normality)
    - [Parametric Efficiency](#parametric-efficiency)
    - [Empirical processes](#empirical-processes)
    - [Semiparametric models and efficiency](#semiparametric-models-and-efficiency)
    - [Supporting Probability and Analysis Results](#supporting-probability-and-analysis-results)
  - [References](#references)



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

| Results | Name | File |
|-----------|------|------|
| vdV (1998), Eq (7.1) — Differentiability in Quadratic Mean | `DifferentiableQuadraticMean` | `DQM/Defs.lean` |
| vdV (1998), §7.2 — quadratic-mean-differentiable path | `QMDPath` | `Core/QMDPath.lean` |
| vdV (1998), §8.5 — regular estimator sequence | `RegularEstimatorSequence` | `ParametricFamily/RegularEstimator.lean` |
| vdV (1998), §25.3 — regular estimator (semiparametric) | `IsRegularEstimator` / `IsRegularEstimator_vec` | `LowerBounds/RegularEstimator.lean`, `LowerBounds/RegularEstimatorVec.lean` |
| vdV (1998), §8.7 — bowl-shaped loss function | `BowlShaped` | `ForMathlib/BowlShaped.lean` |
| vdV (1998), §25.3 — tangent set / tangent space | `TangentSpec` | `Core/TangentAbstract.lean` |
| vdV (1998), §8.2 — Gaussian shift experiment | `IsGaussianShift` | `Experiment/GaussianShift.lean` |
| vdV (1998), §8.4 — equivariant-in-law estimator | `IsEquivariantInLaw` | `Experiment/EquivariantInLaw.lean` |
| vdV (1998), §19.1 — Glivenko–Cantelli class | `IsPGlivenkoCantelli` | `EmpiricalProcess/GlivenkoCantelli.lean` |
| vdV (1998), §19.2 — Donsker class | `IsPDonsker` | `EmpiricalProcess/Donsker.lean` |
| vdV (1998), §19.2 — ε-bracket | `IsBracket` / `IsEpsBracket` | `EmpiricalProcess/Bracketing.lean` |
| vdV (1998), §19.2 — bracketing number `N_[](ε, F, L_r)` | `HasFiniteBracketingCover` | `EmpiricalProcess/Bracketing.lean` |
| vdV (1998), §19.2 — envelope function | `IsEnvelope` | `EmpiricalProcess/FunctionClass.lean` |
| vdV (1998), §25.6 — coarsening at random | `IsCoarseningAtRandom` | `Operators/CAR.lean` |

### Local Asymptotic Normality

| Results | Name | File |
|-----------|------|------|
| vdV (1998), Eq (7.1) — parametric submodel is differentiable in quadratic mean | `paramSubmodel_DQM` | `ParametricFamily/SubmodelDQM.lean` |
| vdV (1998), Thm 7.2 — local asymptotic normality of the log-likelihood via score and Fisher information | `LAN_expansion` | `LocalAsymptoticNormality/LANExpansion.lean` |

### Parametric Efficiency

| Results | Name | File |
|-----------|------|------|
| vdV (1998), Thm 6.5 — mutual contiguity of local alternative sequences | `contiguous_local_alternatives` | `LocalAsymptoticNormality/AsymptoticRepresentation.lean` |
| vdV (1998), Thm 8.2 — regular estimators satisfy the convergence-of-experiments hypothesis | `regularity_implies_8_2_hypothesis` | `Efficiency/HajekLeCamConvolution.lean` |
| vdV (1998), Thm 8.4 — asymptotic representation via a Gaussian-shift Markov kernel | `LAN_representation_vdV` | `LocalAsymptoticNormality/AsymptoticRepresentation.lean` |
| vdV (1998), Lem 8.5 — Anderson's lemma for Gaussian superlevel sets | `anderson_lemma_set` | `ForMathlib/Anderson.lean` |
| vdV (1998), Thm 8.8 — regular estimator limit factors as a Gaussian convolution | `hajek_le_cam_convolution_theorem` | `Efficiency/HajekLeCamConvolution.lean` |
| vdV (1998), Thm 8.11 — local asymptotic minimax lower bound for the risk | `local_asymptotic_minimax_bound` | `Efficiency/LocalAsymptoticMinimax.lean` |

### Empirical processes

| Results | Name | File |
|-----------|------|------|
| vdV (1998), Thm 19.4 — finite L¹-bracketing implies the Glivenko–Cantelli property | `isPGlivenkoCantelli_of_finite_bracketing_L1` | `EmpiricalProcess/GlivenkoCantelli.lean` |
| vdV (1998), Thm 19.5 — finite bracketing entropy integral implies the Donsker property | `isPDonsker_of_finite_bracketing_entropy_integral` | `EmpiricalProcess/DonskerBracketing.lean` |
| vdV (1998), Lem 19.24 — empirical process at a consistent random argument is negligible | `donsker_random_function_consistency` | `EmpiricalProcess/RandomFunctions.lean` |
| vdV (1998), Thm 19.26 — empirical process convergence under estimated parameters | `empiricalProcess_param_estimation` | `EmpiricalProcess/ParameterEstimation.lean` |
| vdV (1998), Lem 19.32 — Bernstein tail bound for empirical sums | `bernstein_inequality` | `EmpiricalProcess/Maximal.lean` |
| vdV (1998), Lem 19.33 — expected maximum over a finite function class | `finite_sup_bound` | `EmpiricalProcess/Maximal.lean` |
| vdV (1998), Lem 19.34 — bracketing maximal inequality for the empirical process | `maximal_inequality_bracketing` | `EmpiricalProcess/Maximal.lean` |

### Semiparametric models and efficiency

| Results | Name | File |
|-----------|------|------|
| vdV (1998), Lem 25.14 — score is mean-zero and square-integrable | `score_in_L2ZeroMean` | `Core/QMDPath.lean` |
| vdV (1998), Thm 25.18 — efficient influence function is the projection onto the tangent space | `eif_eq_orthogonalProjection` | `Core/EIF.lean` |
| vdV (1998), Lem 25.19 — efficiency bound as a supremum of inner-product ratios | `efficient_bound_eq_sup_ratio` | `Core/EIF.lean` |
| vdV (1998), Thm 25.20 — convolution theorem and asymptotic variance lower bound | `semiparametric_convolution_theorem` | `LowerBounds/Convolution.lean` |
| vdV (1998), Thm 25.20 — vector convolution theorem and covariance lower bound | `semiparametric_convolution_theorem_vec` | `LowerBounds/ConvolutionVec.lean` |
| vdV (1998), Thm 25.21 — semiparametric local asymptotic minimax bound | `semiparametric_local_asymptotic_minimax_theorem` | `LowerBounds/LAM.lean` |
| vdV (1998), Thm 25.21 — scalar semiparametric local asymptotic minimax corollary | `semiparametric_local_asymptotic_minimax_theorem_real` | `LowerBounds/LAM.lean` |
| vdV (1998), Eq (25.22) — asymptotically linear estimator with the EIF is efficient | `estimator_semiparametricallyEfficient_of_asympLinear_eif` | `Core/EfficiencyOperational.lean` |
| vdV (1998), Lem 25.25 — efficient influence function from the efficient score | `eif_from_efficientScore` | `StrictModel/EfficientScore.lean` |
| vdV (1998), Eq (25.30) — efficient influence function via the information operator | `eif_via_information_operator` | `Operators/ScoreOperator.lean` |
| vdV (1998), Thm 25.31 — efficient influence function via the adjoint score equation | `eif_via_adjoint_equation` | `Operators/ScoreOperator.lean` |
| vdV (1998), Eq (25.33) — efficient score as score minus its nuisance projection | `efficientScore_projection_formula` | `Operators/ScoreOperator.lean` |
| vdV (1998), Cor 25.42 — influence function by subtracting the nuisance projection | `influence_on_sup_of_subtract_proj_nuisance` | `Core/EIF.lean` |
| vdV (1998), Thm 25.54 — efficient-score Z-estimator is semiparametrically efficient | `zEstimator_semiparametricallyEfficient` | `Asymptotics/ZEstimator.lean` |
| vdV (1998), Thm 25.57 — one-step corrected estimator is semiparametrically efficient | `oneStep_semiparametricallyEfficient` | `Asymptotics/OneStep.lean` |
| vdV (1998), Thm 25.59 — Z-estimator expansion with explicit bias–residual term | `zEstimator_biasResidual_expansion` | `Asymptotics/ZEstimator.lean` |
| vdV (1998), Thm 25.77 — least-favorable-path MLE is semiparametrically efficient | `mle_semiparametricallyEfficient` | `Asymptotics/LeastFavorable.lean` |

### Supporting Probability and Analysis Results

We also formalize the following standard results in probability and
analysis that are used as load-bearing infrastructure by the
asymptotic-statistics.

| Results | Name | File |
|--------|------|------|
| Prékopa–Leindler inequality on ℝⁿ [\[Prékopa 1973\]](#ref-prekopa1973) | `prekopaLeindler` | `ForMathlib/PrekopaLeindler.lean` |
| Anderson's lemma, independent coordinates [\[Anderson 1955\]](#ref-anderson1955) | `anderson_lemma_independent` | `ForMathlib/Anderson.lean` |
| Le Cam's first lemma (mutual contiguity from asymptotic log-normality) [\[vdV 1998, §6.4\]](#ref-vdv1998) | `mutuallyContiguous_of_asymptotically_log_normal` | `ForMathlib/Contiguity.lean` |
| Le Cam's third lemma (weak limit transport under contiguity) [\[vdV 1998, §6.7\]](#ref-vdv1998) | `weak_limit_under_Q_of_lecam_third` | `ForMathlib/Contiguity.lean` |
| Lévy continuity theorem for vector-valued laws [\[Lévy 1925\]](#ref-levy1925) | `levyMpass_vec` | `ForMathlib/LevyMpassVec.lean` |
| Multivariate CLT via characteristic functions [\[Cramér–Wold 1936\]](#ref-cramerwold1936) | `tendstoInDistribution_multivariate_clt` | `ForMathlib/MultivariateCLT.lean` |
| Cramér–Wold device for weak convergence [\[Cramér–Wold 1936\]](#ref-cramerwold1936) | `cramerWold_weakConverges` | `ForMathlib/CramerWoldWeakConverges.lean` |
| Slutsky's theorem [\[Slutsky 1925\]](#ref-slutsky1925) | `WeakConverges.slutsky_of_tendstoInMeasure_dist` | `ForMathlib/Slutsky.lean` |
| Doob L² isometry: conditional expectation as L²(σ-sub-algebra) ≃ L²(comap) [\[Doob 1953\]](#ref-doob1953) | `doobL2Equiv` | `ForMathlib/CondExpL2.lean` |
| Doob-style identification `Lᵖ(μ|_𝒢) ≃ Lᵖ(map μ)` [\[Doob 1953\]](#ref-doob1953) | `lpTrimComapToLpMap` | `ForMathlib/CondExpL2.lean` |

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
