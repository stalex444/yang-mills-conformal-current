import YM.Work.A01.Conserve

/-!
# Conformal Killing fields on the release's `E4`

`conformal` is the Euclidean conformal Killing equation in dimension four, written with the
release's directional derivative `YM.Analysis.D`, coordinate vectors `YM.basis` and index type
`YM.Axis`. The release's `YM.Work.A01.killing` is the special case of zero divergence.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01
open scoped BigOperators ContDiff

/-- The conformal Killing equation on `E4` (metric `δ`, dimension four). -/
def conformal (V : E4 → E4) : Prop := ∀ (a b : Axis) (x : E4),
  D (basis a) (fun y => V y b) x + D (basis b) (fun y => V y a) x =
    if a = b then (1/2 : ℝ) * ∑ c : Axis, D (basis c) (fun y => V y c) x else 0

/-- A Killing field (the release's predicate) has vanishing diagonal derivatives. -/
theorem killing_diagonal {V : E4 → E4} (hk : killing V) (a : Axis) (x : E4) :
    D (basis a) (fun y => V y a) x = 0 := by
  have h := hk a a x
  linarith

/-- A Killing field has zero divergence. -/
theorem killing_divergence {V : E4 → E4} (hk : killing V) (x : E4) :
    ∑ c : Axis, D (basis c) (fun y => V y c) x = 0 :=
  Finset.sum_eq_zero fun c _ => killing_diagonal hk c x

/-- A Killing field is conformal (with zero divergence, `killing_divergence`). -/
theorem killing_conformal {V : E4 → E4} (hk : killing V) : conformal V := by
  intro a b x
  rw [killing_divergence hk x, mul_zero, ite_self, hk a b x, neg_add_cancel]

/-- Coordinate derivatives of the identity field. -/
theorem D_coordinate (a b : Axis) (x : E4) :
    D (basis a) (fun y : E4 => y b) x = if b = a then 1 else 0 := by
  have h : (fun y : E4 => y b) = ⇑(EuclideanSpace.proj b : E4 →L[ℝ] ℝ) := rfl
  rw [h]; unfold D
  rw [ContinuousLinearMap.fderiv]
  exact basis_eq a b

/-- The dilation field `V y = y` has divergence four. -/
theorem dilation_divergence (x : E4) :
    ∑ c : Axis, D (basis c) (fun y : E4 => (fun z : E4 => z) y c) x = 4 := by
  simp [D_coordinate]

/-- The dilation field `V y = y` is conformal. -/
theorem dilation_conformal : conformal (fun y : E4 => y) := by
  intro a b x
  rw [dilation_divergence x]
  change D (basis a) (fun y : E4 => y b) x + D (basis b) (fun y : E4 => y a) x = _
  rw [D_coordinate, D_coordinate]
  by_cases h : a = b
  · subst h; norm_num
  · rw [if_neg h, if_neg (Ne.symm h), if_neg h, add_zero]

/-- The index contraction behind the divergence identity: a symmetric array contracted with an
array whose symmetric part is pure trace sees only a quarter of that trace. -/
theorem contraction {c : Axis → Axis → ℝ} {F : Axis → Axis → ℂ} (hF : ∀ a b, F a b = F b a)
    (hc : ∀ a b, c a b + c b a = if a = b then (1/2 : ℝ) * ∑ e : Axis, c e e else 0) :
    ∑ a : Axis, ∑ b : Axis, c a b • F a b =
      ((1/4 : ℝ) * ∑ e : Axis, c e e) • ∑ a : Axis, F a a := by
  have h1 : ∑ a : Axis, ∑ b : Axis, c a b • F a b = ∑ a : Axis, ∑ b : Axis, c b a • F a b := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hF b a]
  have h2 : ∑ a : Axis, ∑ b : Axis, c a b • F a b + ∑ a : Axis, ∑ b : Axis, c a b • F a b =
      ((1/2 : ℝ) * ∑ e : Axis, c e e) • ∑ a : Axis, F a a := by
    conv_lhs => rhs; rw [h1]
    rw [← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_smul, hc]
    simp
  rw [Complex.real_smul] at h2 ⊢
  push_cast at h2 ⊢
  linear_combination (1/2 : ℂ) * h2

end PDTAdapters
