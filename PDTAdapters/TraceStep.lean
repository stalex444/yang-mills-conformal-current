import PDTAdapters.General
import PDTAdapters.Divergence
import YM.TraceExtension.WilsonTrace
import YM.Ground.Lean

/-!
# The divergence of the dilation current with a centred spectator

Separated-point statements on the release's definitions `YM.TraceExtension.selected`, `center`,
`opposed` and `euclidean` (`YM/TraceExtension/WilsonTrace.lean`).

* `at_unitIn` — the unit label in the front slot of a moment read in a second table.
* `centered_front` — against a centred spectator, the trace label in the front slot may be
  replaced by its centred form.
* `dilation_divergence_centerIn` — general table, every separated pair: the divergence of the
  dilation current against the spectator `theta T J` is the two-point moment of `theta T J` at
  that pair.
* `selected_dilation_divergence` — on a `Spec.Final`, at the configuration `opposed r` with
  `0 < r`, that divergence is `euclidean F r`. The factor is `1`.
  `selected_dilation_divergence_of_ne` is the same for every `r ≠ 0`.
* `selected_axis_shape`, `selected_dilation_divergence_at` — at every separated pair `(y, x 0)`
  that divergence is `euclidean F ‖y - x 0‖`. `selected_axis_shape` is the statement of the
  release's `YM.Trace.Verse.axis_shape` in `useAt` form; its module is not imported here, and the
  proof follows the text of that declaration.
* `selected_dilation_rate`, `selected_dilation_not_conserved` — consequences of a hypothesis on
  the function `euclidean F`, with a real constant `c`. The hypothesis is an assumption of these
  two theorems; nothing in this file proves it for any `F`, and nothing in this file constructs
  an `F : Spec.Final C f S`. By `selected_dilation_divergence`, the conclusion of
  `selected_dilation_not_conserved` is `euclidean F r ≠ 0` for `0 < r < r₀`.
* `rate_ne_zero`, `rate_zero_control` — the step from the rate to non-vanishing for an arbitrary
  `f : ℝ → ℂ`, and the zero function with `c = 0`, for which the rate hypothesis holds and the
  non-vanishing conclusion fails.

All configurations are in `conf` (distinct points). Nothing here concerns coincident points.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01 YM.TraceExtension YM.Spec Filter
open scoped BigOperators ContDiff Topology

section general
variable {G : Gauge} {L : Register G} {S T : Table L} {n : ℕ}

/-- The release's `Table.at_unit` with the moments read in a second table `T` that respects `S`:
the unit label in the front slot drops out. -/
theorem at_unitIn (hr : T.respects S) (ht : T.Hierarchy) {x : Points (n+1)} (hx : x ∈ conf (n+1))
    (v : Fin n → S.Tag) (d : ℕ) :
    S.useAt T x (Fin.cons ⟨d,S.unit d⟩ v) = S.useAt T (Points.tail x) v := by
  let w : Fin n → L.Token := fun i => ⟨(v i).1,S.representative _ (v i).2⟩
  let F := Fin.cons (α := fun _ : Fin (n+1) => L.Token) (L.one d) w
  have he (i) : S.classTokens (w i) = v i := by
    change Sigma.mk (v i).1 (S.project _ (S.representative _ _)) = v i
    rw [S.rep]
  rw [show (Fin.cons (α := fun _ => S.Tag) ⟨d,S.unit d⟩ v) = S.classTokens ∘ F by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [F,Function.comp_apply,Fin.cons_zero]; rfl
    · simp only [F,Function.comp_apply, Fin.cons_succ,he], S.at_project T ht.laws.toSymmetric hr hx,
    ht.laws.unital hx d w]
  rfl

/-- Against the centred spectator `theta T J`, the trace label `stressTrace J` in the front slot
reads the same as `theta T J`: the difference is a multiple of the unit, whose contribution is the
one-point moment of `theta T J`, which is zero. -/
theorem centered_front (hr : T.respects S) (ht : T.Hierarchy) (J : S.Stress) {x : Points 1} {y : E4}
    (hy : Points.cons y x ∈ conf 2) :
    S.useAt T (Points.cons y x)
        (Fin.cons ⟨4, stressTrace J⟩ (fun _ : Fin 1 => (⟨4, theta T J⟩ : S.Tag))) =
      S.useAt T (Points.cons y x) (fun _ : Fin 2 => (⟨4, theta T J⟩ : S.Tag)) := by
  have hc : (fun _ : Fin 2 => (⟨4, theta T J⟩ : S.Tag)) =
      Fin.cons (α := fun _ => S.Tag) ⟨4, theta T J⟩ (fun _ : Fin 1 => (⟨4, theta T J⟩ : S.Tag)) := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hs : stressTrace J = theta T J + euclideanVEV S T (stressTrace J) • S.unit 4 := by
    unfold theta centerIn; abel
  rw [hc, ← frontIn_eval, ← frontIn_eval]
  conv_lhs => rw [hs]
  rw [map_add, map_smul, frontIn_eval, frontIn_eval, at_unitIn hr ht hy,
    vev_coordinates ht.translations, show euclideanVEV S T (theta T J) = 0 from centerIn_vac hr ht _]
  simp

/-- **General table, every separated pair.** For a table `T` that respects `S` and is a
`Hierarchy`, with the plan `W` realizing its derivatives and `J` conserved: the divergence of the
dilation current of `J`, read in `T` against the single spectator `theta T J` at `x`, taken at
`y`, is the two-point moment of `theta T J` at the pair `(y, x 0)`. -/
theorem dilation_divergence_centerIn (hr : T.respects S) (ht : T.Hierarchy) (W : DiffPlan S)
    (hd : W.Derivatives T) {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J)
    {x : Points 1} {y : E4} (hy : Points.cons y x ∈ conf 2) :
    ∑ a : Axis, D (basis a) (currentIn T J (fun z : E4 => z) x
        (fun _ : Fin 1 => (⟨4, theta T J⟩ : S.Tag)) a) y =
      S.useAt T (Points.cons y x) (fun _ : Fin 2 => (⟨4, theta T J⟩ : S.Tag)) := by
  rw [dilation_divergence_traceIn T ht.smooth W hd J hJ _ hy, centered_front hr ht J hy]
end general

section rate

/-- For any `f : ℝ → ℂ`: if `s⁸ (log s⁻¹)² • f s` tends to a nonzero real `c` as `s → 0⁺`, then
`f` has no zero on some interval `(0, r₀)`. -/
theorem rate_ne_zero {f : ℝ → ℂ} (c : ℝ)
    (h : Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) • f s) (𝓝[>] 0) (𝓝 (c : ℂ)))
    (hc : c ≠ 0) : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → f r ≠ 0 := by
  have hne : ∀ᶠ s in 𝓝[>] (0:ℝ), ((s^8 * (Real.log s⁻¹)^2) : ℝ) • f s ≠ 0 :=
    h.eventually_ne (by exact_mod_cast hc)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hne
  exact ⟨u, hu, fun r hr hru h0 => hsub ⟨hr, hru⟩ (by simp [h0])⟩

/-- **Control.** The hypothesis `c ≠ 0` of `rate_ne_zero` cannot be dropped: for the zero function
and `c = 0` the rate hypothesis holds and the conclusion fails. -/
theorem rate_zero_control :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) • (0 : ℝ → ℂ) s) (𝓝[>] 0)
        (𝓝 ((0 : ℝ) : ℂ)) ∧
      ¬ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ → (0 : ℝ → ℂ) r ≠ 0 := by
  refine ⟨?_, ?_⟩
  · simp only [Pi.zero_apply, smul_zero, Complex.ofReal_zero]
    exact tendsto_const_nhds
  · rintro ⟨r₀, h0, h⟩
    exact h (r₀ / 2) (half_pos h0) (half_lt_self h0) rfl

end rate

variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : Spec.Final C f S)

/-- The release's configuration `opposed r` is separated when `0 < r`. -/
theorem opposed_conf {r : ℝ} (hr : 0 < r) : opposed r ∈ conf 2 :=
  Boundary.clear (east_pairH (half_pos hr)) 0

/-- `opposed r` is separated for every `r ≠ 0`: its two points have time coordinates `-(r/2)`
and `r/2`. -/
theorem opposed_conf_of_ne {r : ℝ} (hr : r ≠ 0) : opposed r ∈ conf 2 := by
  intro i j hij
  have he : pairH (r/2) i = pairH (r/2) j := by
    have he := congr_arg time hij
    simpa [opposed, Boundary.place] using he
  fin_cases i <;> fin_cases j
  · rfl
  · exfalso; apply hr
    simp only [Fin.zero_eta, Fin.mk_one, pairH_zero, pairH_one] at he; linarith
  · exfalso; apply hr
    simp only [Fin.zero_eta, Fin.mk_one, pairH_zero, pairH_one] at he; linarith
  · rfl

/-- The identity of `selected_dilation_divergence` for every `r ≠ 0`. -/
theorem selected_dilation_divergence_of_ne {r : ℝ} (hr : r ≠ 0) :
    ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
        (Points.tail (opposed r)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed r 0)
      = euclidean F r := by
  have hy : Points.cons (opposed r 0) (Points.tail (opposed r)) ∈ conf 2 := by
    rw [cons_head_tail]; exact opposed_conf_of_ne hr
  have h := dilation_divergence_centerIn (T := selected F) (selected_respects F)
    (selected_hierarchy F) F.sector.derivatives (F.phase.phase.calculus _) F.sector.energy
    F.phase.transport.conserved hy
  rw [cons_head_tail] at h
  exact h

/-- **At the release's configuration.** In the phase `selected F`, the divergence of the dilation
current of `F.sector.energy` against the spectator `center F`, at the configuration `opposed r`
with `0 < r`, is `euclidean F r`. -/
theorem selected_dilation_divergence {r : ℝ} (hr : 0 < r) :
    ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
        (Points.tail (opposed r)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed r 0)
      = euclidean F r :=
  selected_dilation_divergence_of_ne F hr.ne'

/-- The statement of the release's `YM.Trace.Verse.axis_shape`
(`YM/TraceExtension/Verse/Day.lean`), in `useAt` form: at every separated pair the two-point
moment of `center F` in `selected F` is `euclidean F` at the distance of the pair. That module is
not imported here; the proof follows the text of that declaration, from `OS.Ground.columns`, the
orientation law `sym` of the selection certificate, `trace_turn` and translation invariance. -/
theorem selected_axis_shape {x : Points 2} (h : x ∈ conf 2) :
    S.useAt (selected F) x (fun _ : Fin 2 => (⟨4, center F⟩ : S.Tag)) =
      euclidean F ‖x 0 - x 1‖ := by
  let X := F.sector.turns
  let Y := fun _ : Fin 2 => (⟨4, center F⟩ : S.Tag)
  let u := x 0 - x 1
  let t := ‖x 0 - x 1‖
  let v := (-t) • basis timeAxis
  obtain ⟨K, hK⟩ := OS.Ground.columns
    (Submodule.reflection (Submodule.span ℝ ({u - v} : Set E4)).orthogonal)
  have he : ‖u‖ = ‖v‖ := by simp [v, t, u, norm_smul]
  have hw : Ortho.move K (x 0) - Ortho.move K (x 1) = v := by
    change Ortho.motion K _ - Ortho.motion K _ = v
    rw [← map_sub]; change Ortho.move K u = v; rw [hK]; exact Submodule.reflection_sub he
  have hu : S.useAt (selected F) (Points.move K x) Y = S.useAt (selected F) x Y := by
    have hx : X.label K ∘ Y = Y := funext fun i => congr_arg (Sigma.mk 4)
      (trace_turn F.phase.transport.spin F.phase.transport.spots K)
    have hh : S.useAt (selected F) (Points.move K x) (X.label K ∘ Y) = _ :=
      F.phase.phase.sym F.α.atPoint 2 Y x h K
    rw [hx] at hh; exact hh
  have ht : opposed t 0 - opposed t 1 = v := by
    ext1 i; fin_cases i <;> simp [opposed, v, Bid.bothH, Boundary.place, pairH, YM.position]
    · change (0:ℝ) - 0 = -(0:ℝ); ring
    · change (0:ℝ) - 0 = -(0:ℝ); ring
    change -(t/2) - t/2 = -t; ring
  let y := opposed t 1 - Ortho.move K (x 1)
  have hv : Points.across y (Points.move K x) = opposed t := by
    ext1 i; fin_cases i
    · change Ortho.move K (x 0) + y = _; unfold y
      change Ortho.move _ _ + _ = opposed t 0; rw [← sub_eq_zero]
      rw [show Ortho.move K (x 0) + (opposed t 1 - Ortho.move K (x 1)) - opposed t 0 =
        (Ortho.move K (x 0) - Ortho.move K (x 1)) - (opposed t 0 - opposed t 1) from by abel,
        hw, ht, sub_self]
    change Ortho.move K (x 1) + y = _; unfold y; abel
  change S.useAt (selected F) x Y = _
  rw [← hu]; unfold euclidean; rw [← hv]
  exact ((selected_hierarchy F).translations _ _ (Points.move_in K h) y
    (fun _ => ⟨4, S.representative 4 (center F)⟩)).symm

/-- **At every separated pair.** In the phase `selected F`, the divergence of the dilation current
of `F.sector.energy` against the spectator `center F` at `x`, taken at `y` with `y ≠ x 0`, is
`euclidean F ‖y - x 0‖`. -/
theorem selected_dilation_divergence_at {x : Points 1} {y : E4}
    (hy : Points.cons y x ∈ conf 2) :
    ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z) x
        (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) y = euclidean F ‖y - x 0‖ :=
  (dilation_divergence_centerIn (T := selected F) (selected_respects F)
    (selected_hierarchy F) F.sector.derivatives (F.phase.phase.calculus _) F.sector.energy
    F.phase.transport.conserved hy).trans (selected_axis_shape F hy)

/-- **The rate, in hypothesis form.** If `s⁸ (log s⁻¹)² • euclidean F s` tends to a real `c` as
`s → 0⁺`, so does the same multiple of the divergence of the dilation current at `opposed s`. -/
theorem selected_dilation_rate (c : ℝ) (hsd :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) • euclidean F s)
      (𝓝[>] 0) (𝓝 (c : ℂ))
    ) :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
        ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
          (Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed s 0))
      (𝓝[>] 0) (𝓝 (c : ℂ)) :=
  hsd.congr' (by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [selected_dilation_divergence F hs])

/-- **Non-vanishing, in hypothesis form.** Under the same hypothesis with `c ≠ 0`, there is
`r₀ > 0` such that the divergence of the dilation current at `opposed r` is nonzero for every
`0 < r < r₀`. -/
theorem selected_dilation_not_conserved (c : ℝ) (hsd :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) • euclidean F s)
      (𝓝[>] 0) (𝓝 (c : ℂ))
    ) (hc : c ≠ 0) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∑ a : Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
        (Points.tail (opposed r)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) (opposed r 0)
        ≠ 0 :=
  rate_ne_zero c (selected_dilation_rate F c hsd) hc

end PDTAdapters
