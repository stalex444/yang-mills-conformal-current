import PDTAdapters.TraceStep
import YM.Nonperturbative.HeadlineSpec

/-!
# The dilation current under the release's `TraceExclusions`

The theorems of this file take, besides `F : Spec.Final C f S`, one hypothesis
`H : YM.Nonperturbative.Headline.TraceExclusions F`, the release's structure in
`YM/Nonperturbative/HeadlineSpec.lean`. They use two of its fields:

* `H.shortDistance` : `(s⁸ (log s⁻¹)²) • euclidean F s` tends to `Trace.Verse.award G` as
  `s → 0⁺`;
* `H.positive` : `0 < Trace.Verse.award G`.

* `headline_dilation_rate` — from `H.shortDistance`: the same multiple of the divergence of the
  dilation current at `opposed s` (as in `selected_dilation_divergence`) tends to
  `Trace.Verse.award G`. This is `selected_dilation_rate` at `c = Trace.Verse.award G`.
* `headline_dilation_not_conserved` — from `H.shortDistance` and `H.positive`: there is `r₀ > 0`
  such that the divergence of the dilation current at `opposed r` is nonzero for every
  `0 < r < r₀`. This is `selected_dilation_not_conserved` at `c = Trace.Verse.award G`.
* `headline_euclidean_ne_zero` — from `H.shortDistance` and `H.positive`: there is `r₀ > 0` such
  that `euclidean F r ≠ 0` for every `0 < r < r₀`.
* `headline_dilation_not_conserved_at` — from the same two fields: there is `r₀ > 0` such that, at
  every pair `(y, x 0)` with `y ≠ x 0` and `‖y - x 0‖ < r₀`, the divergence at `y` of the dilation
  current against the spectator `center F` at `x` is nonzero.

This file proves no instance of `TraceExclusions` and constructs no `F`. The release's
`YangMills.constructed` states `Headline.TraceExclusions F` for its witness (`Construction.lean`,
read in source; that module is not among those this file was checked against).

The `example` at the end checks in the kernel that the statement of `selected_axis_shape`
(`PDTAdapters/TraceStep.lean`) and that of the release's `YM.Trace.Verse.axis_shape`
(`YM/TraceExtension/Verse/Day.lean`, a module in the import closure of this file) are
definitionally equal.

All configurations are in `conf` (distinct points). Nothing here concerns coincident points.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.TraceExtension YM.Spec Filter
open scoped BigOperators Topology

universe u v
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C f S)

/-- **The rate, from the release's field.** Under `H : Headline.TraceExclusions F`, the multiple
`s⁸ (log s⁻¹)²` of the divergence of the dilation current at `opposed s` tends to
`Trace.Verse.award G` as `s → 0⁺`. The proof applies `selected_dilation_rate` to the field
`H.shortDistance`. -/
theorem headline_dilation_rate (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
        ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
          (Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed s 0))
      (𝓝[>] 0) (𝓝 (Trace.Verse.award G : ℂ)) :=
  selected_dilation_rate F (Trace.Verse.award G) H.shortDistance

/-- **Non-conservation at short distance, from the release's fields.** Under
`H : Headline.TraceExclusions F`, there is `r₀ > 0` such that the divergence of the dilation
current at `opposed r` is nonzero for every `0 < r < r₀`. The proof applies
`selected_dilation_not_conserved` to the fields `H.shortDistance` and `H.positive`. -/
theorem headline_dilation_not_conserved
    (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
        (Points.tail (opposed r)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed r 0)
        ≠ 0 :=
  selected_dilation_not_conserved F _ H.shortDistance H.positive.ne'

/-- **The function `euclidean F` at short distance.** Under `H : Headline.TraceExclusions F`,
there is `r₀ > 0` such that `euclidean F r ≠ 0` for every `0 < r < r₀`. The proof applies
`rate_ne_zero` to the fields `H.shortDistance` and `H.positive`. -/
theorem headline_euclidean_ne_zero (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → euclidean F r ≠ 0 :=
  rate_ne_zero _ H.shortDistance H.positive.ne'

/-- **At every pair at short distance.** Under `H : Headline.TraceExclusions F`, there is
`r₀ > 0` such that, for one point `x` and every `y` with `y ≠ x 0` and `‖y - x 0‖ < r₀`, the
divergence at `y` of the dilation current of `F.sector.energy`, read in `selected F` against the
spectator `center F` at `x`, is nonzero. The proof combines `selected_dilation_divergence_at`
with `headline_euclidean_ne_zero` (the fields `H.shortDistance` and `H.positive`). -/
theorem headline_dilation_not_conserved_at
    (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (x : Points 1) (y : E4), y ≠ x 0 → ‖y - x 0‖ < r₀ →
      ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z) x
        (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) y ≠ 0 := by
  obtain ⟨r₀, h0, hr⟩ := headline_euclidean_ne_zero F H
  refine ⟨r₀, h0, fun x y hne hlt => ?_⟩
  have hy : Points.cons y x ∈ conf 2 := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (by simpa [Points.cons] using hij) hne
    · exact absurd (by simpa [Points.cons] using hij.symm) hne
    · rfl
  rw [selected_dilation_divergence_at F hy]
  exact hr _ (norm_pos_iff.2 (sub_ne_zero.2 hne)) hlt

/-- The statements of `selected_axis_shape` and of the release's `YM.Trace.Verse.axis_shape` are
definitionally equal (both sides are proofs; the kernel accepts `rfl`). -/
example : @selected_axis_shape = @YM.Trace.Verse.axis_shape := rfl

end PDTAdapters
