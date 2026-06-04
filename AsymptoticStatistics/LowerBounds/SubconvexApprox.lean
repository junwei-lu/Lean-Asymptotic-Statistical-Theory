import AsymptoticStatistics.ForMathlib.BowlShaped
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Bounded subconvex approximation from below

Every subconvex (bowl-shaped) loss is monotonically approximable from below by
**bounded subconvex** losses. This reduces the local asymptotic minimax bound for a
general subconvex `ℓ` to the bounded case: apply the bounded case to `ℓ_M = ℓ ∧ M`
and let `M ↑ ∞` by monotone convergence, since `ℓ_M` is again subconvex.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3,
proof of Theorem 25.21.

The construction is the canonical truncation `ℓ_seq M x := ℓ x ⊓ (M : ℝ≥0∞)`, which
is exactly what the book uses; sublevel-set preservation is `BowlShaped.truncate`.
Only bounded + subconvex + monotone convergence is needed, so uniform continuity is
not required of the truncations.

Headline declaration: `subconvex_approx`.
-/

open Filter Topology MeasureTheory
open scoped ENNReal

namespace AsymptoticStatistics.LowerBounds.SubconvexApprox

open AsymptoticStatistics

variable {k : ℕ}

-- via `borelize`; this is the standard route to expose the instance for
-- `BowlShaped`'s `[MeasurableSpace E]` requirement.
attribute [local instance] borel

/-- *Bounded subconvex approximation from below.* Every nonneg subconvex
(bowl-shaped) loss `ℓ : ℝᵏ → ℝ≥0∞` admits a sequence `ℓ_seq M : ℝᵏ → ℝ≥0∞`
of **bounded subconvex** functions with `ℓ_seq M x ↑ ℓ x` pointwise.

The construction is the canonical truncation `ℓ_seq M x := ℓ x ⊓ M` used
verbatim in van der Vaart's proof of Theorem 25.21.

Reference: vdV §25.3, proof of Theorem 25.21.

The "bounded" clause is encoded as `B M ≠ ∞`: a finite cap on `ℓ_seq M`.
Uniform continuity of the truncations is not needed: the book's argument
requires only bounded + subconvex + monotone convergence. -/
theorem subconvex_approx
    (ℓ : EuclideanSpace ℝ (Fin k) → ℝ≥0∞)
    (hℓ_sub : BowlShaped ℓ) :
    ∃ (ℓ_seq : ℕ → EuclideanSpace ℝ (Fin k) → ℝ≥0∞)
      (B : ℕ → ℝ≥0∞),
      -- (a) Each ℓ_seq M is bounded above by a finite cap `B M`.
      (∀ M, B M ≠ ∞) ∧
      (∀ M x, ℓ_seq M x ≤ B M) ∧
      -- (c) Each ℓ_seq M is subconvex (bowl-shaped).
      (∀ M, BowlShaped (ℓ_seq M)) ∧
      -- (d) Pointwise monotone: ℓ_seq M x ≤ ℓ_seq (M+1) x.
      (∀ M x, ℓ_seq M x ≤ ℓ_seq (M + 1) x) ∧
      -- (e) Pointwise lower bound: ℓ_seq M ≤ ℓ.
      (∀ M x, ℓ_seq M x ≤ ℓ x) ∧
      -- (f) Pointwise limit: ℓ_seq M x ↑ ℓ x as M → ∞.
      (∀ x, Tendsto (fun M => ℓ_seq M x) atTop (𝓝 (ℓ x))) := by
  -- The construction: standard truncation `ℓ_seq M x := ℓ x ⊓ M`.
  refine ⟨fun M x => ℓ x ⊓ (M : ℝ≥0∞), fun M => (M : ℝ≥0∞), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a₁) `B M = M ≠ ∞` since `M : ℕ` casts finitely.
    intro M
    exact ENNReal.natCast_ne_top M
  · -- (a₂) `ℓ x ⊓ M ≤ M` by `inf_le_right`.
    intro M x
    exact inf_le_right
  · -- (c) Bowl-shaped: direct from `BowlShaped.truncate`.
    intro M
    exact hℓ_sub.truncate (M : ℝ≥0∞)
  · -- (d) Monotone in `M`: `ℓ x ⊓ M ≤ ℓ x ⊓ (M+1)` since `(M : ℝ≥0∞) ≤ M+1`.
    intro M x
    have hMle : (M : ℝ≥0∞) ≤ ((M + 1 : ℕ) : ℝ≥0∞) := by
      exact_mod_cast Nat.le_succ M
    exact inf_le_inf_left (ℓ x) hMle
  · -- (e) `ℓ x ⊓ M ≤ ℓ x` by `inf_le_left`.
    intro M x
    exact inf_le_left
  · -- (f) `Tendsto (fun M => ℓ x ⊓ M) atTop (𝓝 (ℓ x))`.
    -- The sequence `M ↦ ℓ x ⊓ M` is monotone (clause (d)) so converges to
    -- its supremum; the supremum equals `ℓ x ⊓ (⨆ M, M) = ℓ x ⊓ ∞ = ℓ x`
    -- by complete-distributivity (`inf_iSup_eq`) and `ENNReal.iSup_natCast`.
    intro x
    have h_mono : Monotone (fun M : ℕ => ℓ x ⊓ (M : ℝ≥0∞)) := by
      intro a b hab
      have : (a : ℝ≥0∞) ≤ (b : ℝ≥0∞) := by exact_mod_cast hab
      exact inf_le_inf_left (ℓ x) this
    have h_to_sup : Tendsto (fun M : ℕ => ℓ x ⊓ (M : ℝ≥0∞)) atTop
        (𝓝 (⨆ M : ℕ, ℓ x ⊓ (M : ℝ≥0∞))) :=
      tendsto_atTop_iSup h_mono
    -- Identify the supremum with `ℓ x`.
    have h_sup_eq : (⨆ M : ℕ, ℓ x ⊓ (M : ℝ≥0∞)) = ℓ x := by
      have h_distrib : (⨆ M : ℕ, ℓ x ⊓ (M : ℝ≥0∞))
          = ℓ x ⊓ (⨆ M : ℕ, (M : ℝ≥0∞)) := (inf_iSup_eq _ _).symm
      rw [h_distrib, ENNReal.iSup_natCast]
      simp
    rw [h_sup_eq] at h_to_sup
    exact h_to_sup

end AsymptoticStatistics.LowerBounds.SubconvexApprox
