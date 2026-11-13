import YM.Gauge.Casimir

/-!
# The determinant of an invariant symmetric endomorphism of the colour space

Stated on the release's gauge type `YM.Gauge`, its colour space `G.Color`, its bracket `G.ad`,
its simplicity predicate `G.Simple` and its dimension `G.lieDim`.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Gauge
open scoped InnerProductSpace

/-- A symmetric endomorphism of the colour space that commutes with every `G.ad x` is a scalar,
and its determinant is that scalar to the power `G.lieDim`. The determinant clause is an immediate
consequence of `A = c • 1`. The symmetry hypothesis is part of the statement: this is not a claim
about every commuting operator. -/
theorem det_invariant (G : Gauge) (h : G.Simple) (A : Module.End ℝ G.Color) (hs : A.IsSymmetric)
    (hc : ∀ x y, A (G.ad x y) = G.ad x (A y)) :
    ∃ c : ℝ, A = c • (1 : Module.End ℝ G.Color) ∧ LinearMap.det A = c ^ G.lieDim := by
  obtain ⟨c, hB⟩ := invariant_scalar h ((innerₗ G.Color).comp A)
    (fun x y => by
      change ⟪A x, y⟫_ℝ = ⟪A y, x⟫_ℝ
      exact (hs x y).trans (real_inner_comm (A y) x))
    (fun x y z => by
      change ⟪A (G.ad x y), z⟫_ℝ = -⟪A y, G.ad x z⟫_ℝ
      rw [hc, ad_skew])
  have hA : A = c • (1 : Module.End ℝ G.Color) := by
    apply LinearMap.ext
    intro x
    apply ext_inner_right ℝ
    intro y
    have := hB x y
    change ⟪A x, y⟫_ℝ = c * ⟪x, y⟫_ℝ at this
    rw [this, LinearMap.smul_apply, Module.End.one_apply, real_inner_smul_left]
  refine ⟨c, hA, ?_⟩
  rw [hA, LinearMap.det_smul, map_one, mul_one, finrank_euclideanSpace_fin]

end PDTAdapters
