import PDTAdapters.Divergence
import PDTAdapters.General
import PDTAdapters.TraceStep
import YM.Next.MAXWELL.Current

/-!
# The identities on the release's `Spec.Final`, and two facts about `conformal`

The theorems of `PDTAdapters.Divergence` and `PDTAdapters.TraceStep` are stated for a general
table. This file instantiates them on the data of a `F : YM.Spec.Final C f S`, naming the fields
of `F` that supply each hypothesis:

* `final_conformal_divergence`, `final_stressTrace_eq_zero_iff` — on the table `S` itself (the
  unselected table), for the release's own `current` and the stress `F.sector.energy`.
* `final_phase_dilation_divergence_center` — the dilation identity against the centred trace in
  every phase `F.α.ensemble i`; `final_dilation_divergence_center` — the same on `S` itself, with
  the release's `current`.

and relates `conformal` to two predicates of the release:

* `killing_of_conformal`, `killing_iff_conformal` — the release's `YM.Work.A01.killing` is
  `conformal` together with zero divergence at every point.
* `conformal_freeKilling` — a `conformal` field with smooth components satisfies the release's
  component predicate `YM.Maxwell.Free.Killing`.

All configurations are in `conf` (distinct points). No `Spec.Final` is constructed here.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01 YM.TraceExtension YM.Spec
open scoped BigOperators ContDiff

section final
variable {G : Gauge} {C : Family G} {f : Extraction.Order} {S : Table C.book} {n : ℕ}

/-- **On the table of a `Final`.** For `F : Spec.Final C f S`, a conformal Killing field `V` with
smooth components, spectator labels `q` at points `x`, and `y` distinct from the `x i` and the
`x i` pairwise distinct: the divergence at `y` of the release's `current F.sector.energy V x q`
is `(∂·V)(y)/4` times the moment of `S` with the trace label `stressTrace F.sector.energy` at `y`.
This is `conformal_divergence` with its hypotheses supplied by fields of `F`: smoothness of the
table by `F.room.kernel.smooth`, the plan `F.sector.derivatives` realizing the derivatives of `S`
by `F.phase.transport.derivatives`, and conservation of `F.sector.energy` by
`F.phase.transport.conserved`. -/
theorem final_conformal_divergence (F : Spec.Final C f S) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current F.sector.energy V x q a) y =
      ((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y) •
        S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace F.sector.energy⟩ q) :=
  conformal_divergence F.room.kernel.smooth F.sector.derivatives F.phase.transport.derivatives
    F.sector.energy F.phase.transport.conserved V hv hc q hy

/-- **The characterization on the table of a `Final`.** For `F : Spec.Final C f S`, the trace
label `stressTrace F.sector.energy` is zero in `S.Field 4` if and only if the dilation current
`current F.sector.energy (fun z => z)` is divergence-free at every separated configuration, with
every list of spectator labels. This is `stressTrace_eq_zero_iff` with its hypotheses supplied by
`F.room.kernel.laws.toSymmetric`, `F.room.kernel.smooth`, `F.phase.transport.derivatives` and
`F.phase.transport.conserved`. Neither side of the equivalence is asserted. -/
theorem final_stressTrace_eq_zero_iff (F : Spec.Final C f S) :
    stressTrace F.sector.energy = 0 ↔
      ∀ (n : ℕ) (x : Points n) (q : Fin n → S.Tag) (y : E4), Points.cons y x ∈ conf (n+1) →
        ∑ a : Axis, D (basis a) (current F.sector.energy (fun z : E4 => z) x q a) y = 0 :=
  stressTrace_eq_zero_iff F.room.kernel.laws.toSymmetric F.room.kernel.smooth F.sector.derivatives
    F.phase.transport.derivatives F.sector.energy F.phase.transport.conserved

/-- **Every phase, against the centred trace.** For `F : Spec.Final C f S`, every index `i` of
the selection `F.α`, one point `x` and `y ≠ x 0`: in the phase table `T = F.α.ensemble i`, with
`θ = theta T F.sector.energy` (the trace label minus its one-point moment in `T` times the unit),
the divergence at `y` of the dilation current of `F.sector.energy` against the spectator `θ` at
`x` is the two-point moment of `θ` in `T` at the pair `(y, x 0)`. This is
`dilation_divergence_centerIn` with `T.respects S` supplied by `F.phase.phase.retains i`,
`T.Hierarchy` by `F.phase.phase.states i`, the derivatives by `F.phase.phase.calculus i` and
conservation by `F.phase.transport.conserved`. -/
theorem final_phase_dilation_divergence_center (F : Spec.Final C f S) (i : F.α.space.X)
    {x : Points 1} {y : E4} (hy : Points.cons y x ∈ conf 2) :
    ∑ a : Axis, D (basis a) (currentIn (F.α.ensemble i) F.sector.energy (fun z : E4 => z) x
        (fun _ : Fin 1 => (⟨4, theta (F.α.ensemble i) F.sector.energy⟩ : S.Tag)) a) y =
      S.useAt (F.α.ensemble i) (Points.cons y x)
        (fun _ : Fin 2 => (⟨4, theta (F.α.ensemble i) F.sector.energy⟩ : S.Tag)) :=
  dilation_divergence_centerIn (fun d => (F.phase.phase.retains i d).symm.le)
    (F.phase.phase.states i) F.sector.derivatives (F.phase.phase.calculus i) F.sector.energy
    F.phase.transport.conserved hy

/-- **The table of a `Final`, against the centred trace.** The same identity on the table `S`
itself, for the release's own `current`: with `θ = theta S F.sector.energy`, the divergence at
`y` of `current F.sector.energy (fun z => z) x` against the spectator `θ` at `x` is the two-point
moment of `θ` in `S` at the pair `(y, x 0)`. The hypotheses of `dilation_divergence_centerIn` at
`T = S` are supplied by `F.room.kernel` (the `Hierarchy`), `F.phase.transport.derivatives` and
`F.phase.transport.conserved`. -/
theorem final_dilation_divergence_center (F : Spec.Final C f S) {x : Points 1} {y : E4}
    (hy : Points.cons y x ∈ conf 2) :
    ∑ a : Axis, D (basis a) (current F.sector.energy (fun z : E4 => z) x
        (fun _ : Fin 1 => (⟨4, theta S F.sector.energy⟩ : S.Tag)) a) y =
      S.useAt S (Points.cons y x) (fun _ : Fin 2 => (⟨4, theta S F.sector.energy⟩ : S.Tag)) :=
  dilation_divergence_centerIn (T := S) (fun _ => le_rfl) F.room.kernel F.sector.derivatives
    F.phase.transport.derivatives F.sector.energy F.phase.transport.conserved hy

end final

/-- A conformal Killing field whose divergence vanishes at every point is a Killing field (the
release's `YM.Work.A01.killing`): with `∂·V = 0` the conformal equation reads
`∂_a V_b + ∂_b V_a = 0`. -/
theorem killing_of_conformal {V : E4 → E4} (hc : conformal V)
    (h0 : ∀ x : E4, ∑ c : Axis, D (basis c) (fun y => V y c) x = 0) : killing V := by
  intro a b x
  have h := hc a b x
  rw [h0 x, mul_zero, ite_self] at h
  linarith

/-- The release's `YM.Work.A01.killing` is the conformal Killing equation together with zero
divergence at every point: `∂_a V_b = −∂_b V_a` for all `a`, `b` if and only if
`∂_a V_b + ∂_b V_a = ½ (∂·V) δ_ab` for all `a`, `b` and `∂·V = 0`. The forward direction is
`killing_conformal` and `killing_divergence`; the reverse is `killing_of_conformal`. -/
theorem killing_iff_conformal {V : E4 → E4} :
    killing V ↔
      conformal V ∧ ∀ x : E4, ∑ c : Axis, D (basis c) (fun y => V y c) x = 0 :=
  ⟨fun hk => ⟨killing_conformal hk, killing_divergence hk⟩,
    fun h => killing_of_conformal h.1 h.2⟩

/-- A `conformal` field `V : E4 → E4` with smooth components satisfies the release's predicate
`YM.Maxwell.Free.Killing` (`YM/Next/MAXWELL/Current.lean`) for the family of its components
`fun a x => V x a`: for `a ≠ b` the conformal equation gives `∂_a V_b = −∂_b V_a`, and for
`a = b` it gives `2 ∂_a V_a = ½ ∂·V`, the same value for every `a`. The converse is not proved
here. -/
theorem conformal_freeKilling {V : E4 → E4} (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b))
    (hc : conformal V) : Maxwell.Free.Killing (fun a x => V x a) := by
  refine ⟨hv, fun a b hab x => ?_, fun a b x => ?_⟩
  · have h := hc a b x
    rw [if_neg hab] at h
    change D (basis a) (fun y => V y b) x = - D (basis b) (fun y => V y a) x
    linarith
  · have ha := hc a a x
    have hb := hc b b x
    rw [if_pos rfl] at ha hb
    change D (basis a) (fun y => V y a) x = D (basis b) (fun y => V y b) x
    linarith

end PDTAdapters
