import AsymptoticStatistics.Core.EIF

/-!
# Projection sequence converging to the efficient influence function

An increasing sequence of finite-dimensional subspaces whose orthogonal
projections of the efficient influence function (EIF) converge to it in `L²(P)`.

Reference: van der Vaart, *Asymptotic Statistics* (Cambridge, 1998), §25.3,
the synthesis step in the proof of Theorems 25.20/25.21.

Headline declaration: `proj_seq_to_eif`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace AsymptoticStatistics.LowerBounds.ProjSeqToEif

open AsymptoticStatistics.Core.Hilbert
open AsymptoticStatistics.Core.Pathwise
open AsymptoticStatistics.Core.TangentAbstract

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- *Projection-sequence brick.* If the EIF `ψ̃` lies in the closed linear
span of the tangent set, then there exists an increasing sequence of
finite-dimensional subspaces `V_m ⊆ closure(lin(tangent set))`, each
spanned by finitely many elements of the tangent set itself, such that the
orthogonal projection of `ψ̃` onto `V_m` converges to `ψ̃` in `L²(P)`.

Reference: vdV §25.3, synthesis step in proofs of Theorems 25.20/25.21. The
book asserts this as an immediate consequence of
`ψ̃ ∈ closure(lin(tangent set))` plus separability of `L²(P)`.

Proof: pick a sequence
`a m ∈ Submodule.span ℝ T_set.carrier` with `‖IF_eff - a m‖ < 1/(m+1)`
(possible since `IF_eff` is in the topological closure of that span by
hypothesis); decompose each `a m` as a finite linear combination, picking a
finset `T m ⊆ T_set.carrier`; take `V m := Submodule.span ℝ (⋃_{k≤m} T k)`,
which is finite-dim and contains every `a k` for `k ≤ m`; each projection
`(V m).starProjection IF_eff` is then within `‖IF_eff - a m‖ < 1/(m+1)` of
`IF_eff` by `Submodule.starProjection_minimal` (it minimizes the distance
from `IF_eff` to `V m`).

Edge behavior: when the tangent set is already finite-dim, the sequence
stabilizes — we can take `V_m` constant after some `m₀`. -/
theorem proj_seq_to_eif
    (T_set : TangentSpec P)
    -- (Identifier: ASCII `IF_eff` matches `Core/EIF.lean`'s convention; the
    -- book's `ψ̃` is a base letter + combining diacritic which is not a single
    -- Lean identifier.)
    {IF_eff : ↥(L2ZeroMean P)} (h_mem : IF_eff ∈ tangentSpace T_set) :
    ∃ V : ℕ → Submodule ℝ ↥(L2ZeroMean P),
    ∃ p : ℕ → ↥(L2ZeroMean P),
      -- (a) Each `V m` is contained in the closed linear span.
      (∀ m, V m ≤ tangentSpace T_set) ∧
      -- (b) The sequence is increasing.
      (∀ m, V m ≤ V (m + 1)) ∧
      -- (c) Each `V m` is finite-dimensional.
      (∀ m, FiniteDimensional ℝ (V m)) ∧
      -- (d) Each `V m` is spanned by finitely many vectors from `T_set.carrier`.
      (∀ m, ∃ S : Finset ↥(L2ZeroMean P),
              (↑S : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
              V m = Submodule.span ℝ (↑S : Set ↥(L2ZeroMean P))) ∧
      -- (e) `p m` is the orthogonal projection of `IF_eff` onto `V m`: it lies
      -- in `V m` and the residual `IF_eff - p m` is orthogonal to `V m`. This
      -- avoids threading a `HasOrthogonalProjection` instance through the
      -- IF_eff` once an orthogonal-projection instance on `V m` is in scope,
      -- which is automatic for finite-dim subspaces by clause (c) →
      -- `CompleteSpace` → instance).
      (∀ m, p m ∈ V m ∧ IF_eff - p m ∈ (V m)ᗮ) ∧
      -- (f) The projection sequence `p m` converges to `IF_eff` in `L²(P)`.
      Tendsto (fun m => ‖(p m : ↥(L2ZeroMean P)) - IF_eff‖) atTop (𝓝 0) := by
  classical
  -- Register `L2ZeroMean P` as closed (used implicitly by Mathlib's auto-resolution
  -- of `CompleteSpace ↥(submodule)` from `[IsClosed _]`).
  haveI : IsClosed ((L2ZeroMean P : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    L2ZeroMean_isClosed P
  -- Unfold tangent-space membership to closure-of-span membership.
  have h_clos : IF_eff ∈ closure
      ((Submodule.span ℝ T_set.carrier : Submodule ℝ ↥(L2ZeroMean P)) :
        Set ↥(L2ZeroMean P)) := by
    have := h_mem
    -- `tangentSpace T = (span … T.carrier).topologicalClosure`, whose underlying set
    -- equals `closure (span …)` by `Submodule.topologicalClosure_coe`.
    simpa [tangentSpace, Submodule.topologicalClosure_coe] using this
  -- Step 1: pick approximations `a m ∈ span (T_set.carrier)` with `‖IF_eff - a m‖ < 1/(m+1)`.
  have h_approx : ∀ m : ℕ, ∃ a : ↥(L2ZeroMean P),
      a ∈ (Submodule.span ℝ T_set.carrier : Submodule ℝ ↥(L2ZeroMean P)) ∧
        ‖IF_eff - a‖ < 1 / (m + 1 : ℝ) := by
    intro m
    have hpos : (0 : ℝ) < 1 / (m + 1 : ℝ) := by positivity
    rcases Metric.mem_closure_iff.mp h_clos (1 / (m + 1 : ℝ)) hpos with ⟨a, ha_mem, hdist⟩
    refine ⟨a, ha_mem, ?_⟩
    -- `dist IF_eff a = ‖IF_eff - a‖` (subtype norm reduces to underlying-space norm).
    rwa [← dist_eq_norm]
  -- Choose such an `a m` for each `m`.
  choose a ha_mem ha_dist using h_approx
  -- Step 2: each `a m` is a finite linear combination — pick a finset `T m ⊆ T_set.carrier`
  -- with `a m ∈ span (T m)`.
  have h_finset : ∀ m : ℕ, ∃ Tm : Finset ↥(L2ZeroMean P),
      (↑Tm : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier ∧
        a m ∈ Submodule.span ℝ (↑Tm : Set ↥(L2ZeroMean P)) := fun m =>
    Submodule.mem_span_finite_of_mem_span (ha_mem m)
  choose T hT_sub hT_mem using h_finset
  -- Step 3: define the cumulative finset `S m := ⋃ k ≤ m, T k`.
  let S : ℕ → Finset ↥(L2ZeroMean P) := fun m =>
    (Finset.range (m + 1)).biUnion T
  -- Step 4: define `V m := span ℝ (S m)`.
  let V : ℕ → Submodule ℝ ↥(L2ZeroMean P) := fun m =>
    Submodule.span ℝ (↑(S m) : Set ↥(L2ZeroMean P))
  -- Helper: each element of `S m` is in `T_set.carrier`.
  have hS_sub : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ T_set.carrier := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio] at hx
    rcases hx with ⟨k, _, hkx⟩
    exact hT_sub k hkx
  -- Helper: monotone in `m`.
  have hS_mono : ∀ m, (↑(S m) : Set ↥(L2ZeroMean P)) ⊆ (↑(S (m + 1)) : Set _) := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio] at hx ⊢
    rcases hx with ⟨k, hk, hkx⟩
    exact ⟨k, by omega, hkx⟩
  -- Helper: `T m ⊆ S m` (as sets).
  have hT_in_S : ∀ m, (↑(T m) : Set ↥(L2ZeroMean P)) ⊆ (↑(S m) : Set _) := by
    intro m x hx
    simp only [S, Finset.coe_biUnion, Finset.coe_range, Set.mem_iUnion,
      Set.mem_Iio]
    exact ⟨m, by omega, hx⟩
  -- Each `V m` is finite-dimensional (instance from `FiniteDimensional.span_finset`).
  have hV_findim : ∀ m, FiniteDimensional ℝ (V m) := fun m =>
    @FiniteDimensional.span_finset ℝ ↥(L2ZeroMean P) _ _ _ (S m)
  -- Each `V m` therefore has a complete-space instance, via
  -- `FiniteDimensional.complete` (finite-dim normed space over `ℝ` ⇒ complete).
  -- We need `IsUniformAddGroup ↥(V m)` for the chain to resolve;
  -- it follows from `AddSubgroup.isUniformAddGroup` once the underlying
  -- `IsUniformAddGroup ↥(L2ZeroMean P)` is in scope.
  haveI hUG_L2 : IsUniformAddGroup ↥(L2ZeroMean P) :=
    (L2ZeroMean P).toAddSubgroup.isUniformAddGroup
  have hV_complete : ∀ m, CompleteSpace (V m) := fun m =>
    haveI := hV_findim m
    haveI : IsUniformAddGroup ↥(V m) := (V m).toAddSubgroup.isUniformAddGroup
    @FiniteDimensional.complete ℝ ↥(V m) _ _ _ _ _ _ _ _ _
  -- Each `V m` therefore has an orthogonal-projection instance.
  have hV_proj : ∀ m, (V m).HasOrthogonalProjection := fun m =>
    @Submodule.HasOrthogonalProjection.ofCompleteSpace _ _ _ _ _ (V m)
      (hV_complete m)
  -- Each `V m` is contained in `Submodule.span ℝ T_set.carrier`, hence in the tangent space.
  have hV_le : ∀ m, V m ≤ tangentSpace T_set := by
    intro m
    have hspan : V m ≤ Submodule.span ℝ T_set.carrier :=
      Submodule.span_mono (hS_sub m)
    refine hspan.trans ?_
    -- The span is contained in its topological closure.
    exact (Submodule.span ℝ T_set.carrier).le_topologicalClosure
  -- The sequence is increasing.
  have hV_inc : ∀ m, V m ≤ V (m + 1) := fun m =>
    Submodule.span_mono (hS_mono m)
  -- Each `a m` is in `V m`: since `T m ⊆ S m`, `span (T m) ≤ span (S m)`.
  have ha_in_V : ∀ m, a m ∈ V m := fun m =>
    Submodule.span_mono (hT_in_S m) (hT_mem m)
  -- Step 5: define the projection sequence.
  let p : ℕ → ↥(L2ZeroMean P) := fun m =>
    haveI := hV_proj m; (V m).starProjection (IF_eff)
  -- Convergence: `‖IF_eff - p m‖ ≤ ‖IF_eff - a m‖ < 1/(m+1) → 0`.
  have h_proj_bound : ∀ m, ‖IF_eff - p m‖ ≤ ‖IF_eff - a m‖ := by
    intro m
    haveI := hV_proj m
    -- `‖IF_eff - p m‖ = ⨅ x : V m, ‖IF_eff - x‖ ≤ ‖IF_eff - a m‖` since `a m ∈ V m`.
    rw [show p m = (V m).starProjection IF_eff from rfl,
      Submodule.starProjection_minimal IF_eff]
    refine ciInf_le ⟨0, ?_⟩ (⟨a m, ha_in_V m⟩ : V m)
    rintro _ ⟨x, rfl⟩
    exact norm_nonneg _
  -- Combine with the rate `1/(m+1) → 0` to get convergence.
  have h_inv_tendsto : Tendsto (fun m : ℕ => 1 / (m + 1 : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  -- Build the existential witness.
  refine ⟨V, p, hV_le, hV_inc, hV_findim, ?_, ?_, ?_⟩
  · -- Clause (d): `V m` is spanned by `S m ⊆ T_set.carrier`.
    intro m
    refine ⟨S m, hS_sub m, rfl⟩
  · -- Clause (e): `p m ∈ V m` and `IF_eff - p m ∈ (V m)ᗮ`.
    intro m
    haveI := hV_proj m
    refine ⟨(V m).starProjection_apply_mem IF_eff,
      (V m).sub_starProjection_mem_orthogonal IF_eff⟩
  · -- Clause (f): convergence of the projections.
    -- We have `‖p m - IF_eff‖ = ‖IF_eff - p m‖`. Bound by `‖IF_eff - a m‖ < 1/(m+1)`.
    have h_bound_real : ∀ m, ‖(p m : ↥(L2ZeroMean P)) - IF_eff‖ ≤ 1 / (m + 1 : ℝ) := by
      intro m
      have h1 : ‖(p m : ↥(L2ZeroMean P)) - IF_eff‖ = ‖IF_eff - p m‖ := by
        rw [norm_sub_rev]
      rw [h1]
      exact (h_proj_bound m).trans (ha_dist m).le
    have h_nonneg : ∀ m, 0 ≤ ‖(p m : ↥(L2ZeroMean P)) - IF_eff‖ := fun _ => norm_nonneg _
    -- Squeeze between 0 and `1/(m+1)`.
    refine squeeze_zero h_nonneg h_bound_real h_inv_tendsto

end AsymptoticStatistics.LowerBounds.ProjSeqToEif
