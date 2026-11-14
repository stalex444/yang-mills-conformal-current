# PDTAdapters: the divergence of the stress current against conformal Killing fields, on the definitions of the Wilson Yang–Mills release

An add-on Lean library for the Lean source distribution of the Wilson Yang–Mills construction in
the repository
[`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464),
commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464` ("the release" below; Lean `v4.32.0`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`).
The name `PDTAdapters` is explained under "Provenance and licences".

Every theorem here is a consequence of the release's definitions and theorems; none is used by, or changes, any proof of the release.

Every declaration depends on `propext`, `Classical.choice` and `Quot.sound` only (`Axioms.lean`, `AxiomsOnHeadline.lean`, `AxiomsOnConstructed.lean`, `AxiomsLieDim.lean`; the output is in `BUILD.txt`). `lake build PDTAdapters`, in a checkout of the release prepared as under "Build", prints the axioms of 34 of the theorems. The release's `YM.Work.A01.divergence` is the case `∂·V = 0` of identity 1 below (an `example … := rfl` in `PDTAdapters/Divergence.lean` checks that the two statements are definitionally equal), and every clause of the release's `YangMills.constructed` is a conjunct of `PDTAdapters.constructed_dilation` (`PDTAdapters.constructed_of_constructed_dilation`).

## The results

Notation. `⟨A(y) q(x)⟩` is the moment of a table with the label `A` at the point `y` and labels
`q = (q_1, …, q_n)` at the points `x = (x_1, …, x_n)`; in Lean,
`S.useAt S (Points.cons y x) (Fin.cons ⟨d, A⟩ q)`. `⟨…⟩_T` is the same with the moments of a
second table `T` read on the labels of `S` (`S.useAt T`). The `n + 1` points are pairwise
distinct. Repeated indices are summed over the four Euclidean axes.

**1. Conformal Killing fields.** Let `S` be a smooth table with a derivative plan that realizes
the derivatives of its moments, `J_ab` a stress on it that is conserved in the release's sense
(`YM.Table.Conserved`: symmetric, real, and `∂_a J_ab = 0` as an identity of labels, `∂` being
the plan's derivative), and `V` a field on Euclidean `ℝ⁴` with smooth components and
`∂_a V_b + ∂_b V_a = ½ δ_ab ∂·V`. Then, for `y` distinct from the `x_i`,

    ∂/∂y_a [ V_b(y) ⟨J_ab(y) q(x)⟩ ]  =  ¼ (∂·V)(y) ⟨J_cc(y) q(x)⟩ .

Lean: `PDTAdapters.conformal_divergence` (`PDTAdapters/Divergence.lean`). Its hypotheses are
those of the release's theorem `YM.Work.A01.divergence` with the conformal Killing equation in
place of the Killing equation, and the release's theorem is the case `∂·V = 0`:
`PDTAdapters.divergence_of_conformal_killing` is derived from the identity and its statement is
definitionally equal to that of `YM.Work.A01.divergence` (an `example … := rfl` in the file
checks it), and `PDTAdapters.killing_iff_conformal` proves that a field satisfies the release's
`YM.Work.A01.killing` exactly when it satisfies the conformal equation with `∂·V = 0` at every
point. For the dilation field `V(y) = y` the right side is `⟨J_cc(y) q(x)⟩`
(`PDTAdapters.dilation_divergence_trace`). For every `F : YM.Spec.Final C f S` (the release's structure) the
hypotheses are met by the table `S` itself with the release's own `YM.Work.A01.current` and the
stress `F.sector.energy` (`PDTAdapters.final_conformal_divergence`, with the plan
`F.sector.derivatives` and the fields `F.room.kernel.smooth`, `F.phase.transport.derivatives`,
`F.phase.transport.conserved`); in every phase table `F.α.ensemble i` the same identity holds
with the moments read in that table, for this library's `currentIn`
(`PDTAdapters.final_phase_conformal_divergence`).

**2. The dilation field against the centred trace.** Let `F : YM.Spec.Final C f S`, let `T` be
any of its phase tables `F.α.ensemble i`, `J = F.sector.energy`, and `θ = J_cc − ⟨J_cc⟩_T · 1`
the trace minus its one-point moment in `T` times the unit (`YM.TraceExtension.theta T J`). Then,
for `y ≠ x`,

    ∂/∂y_a [ y_b ⟨J_ab(y) θ(x)⟩_T ]  =  ⟨θ(y) θ(x)⟩_T .

Lean: `PDTAdapters.final_phase_dilation_divergence_center` (`PDTAdapters/OnFinal.lean`), an
instance of `PDTAdapters.dilation_divergence_centerIn` (`PDTAdapters/TraceStep.lean`), which
holds for every conserved `J` and every table `T` with `T.respects S`, `T.Hierarchy` and a plan
realizing its derivatives. In the selected phase the right side is the release's function
`YM.TraceExtension.euclidean F` at the distance of the pair:
`PDTAdapters.selected_dilation_divergence_at` gives `euclidean F ‖y − x‖` (in Lean,
`‖y - x 0‖`). On the table `S` itself, with the release's own `current`, the identity is
`PDTAdapters.final_dilation_divergence_center`.

**3. On the release's construction theorem.** For every simple gauge group `g` and every `b > 0`
there is a family `C` with penalty `b` and `C.Makes` such that, for every order `p`, there are
`q`, `S` and `F : YM.Spec.Final C (p.refine q) S` with `TraceExclusions F` and an `r₀ > 0` such
that the divergence of the dilation current of `F.sector.energy` in the selected phase, against
the centred trace spectator, is nonzero at every separated pair closer than `r₀`
(`PDTAdapters.constructed_dilation_not_conserved`, `PDTAdapters/OnConstructed.lean`). The witness
is that of the release's theorem `YangMills.constructed`: `PDTAdapters.constructed_dilation`
states the release's statement with this conclusion and the short-distance rate appended, for the
same witness. At the release's `YangMills.su2` with `b = 1` the statement holds with no hypothesis
(`PDTAdapters.su2_dilation_not_conserved`). These rest on `PDTAdapters/OnHeadline.lean`, which
proves that for every `F` satisfying the release's `YM.Nonperturbative.Headline.TraceExclusions F`, the
divergence of the dilation current in the selected phase, against the centred trace spectator,
at the pair `opposed s`, times `s⁸ (log s⁻¹)²` tends to `Trace.Verse.award G` as `s → 0⁺`, and that it is nonzero at every
separated pair closer than some `r₀ > 0` (`PDTAdapters.headline_dilation_rate`,
`PDTAdapters.headline_dilation_not_conserved_at`). Neither module is imported by the root; both
are checked against the restored public compiled build of the release (records 4 and 5 of
`BUILD.txt`; see "On the release's `TraceExclusions`" and "On the release's construction
theorem").

The library also contains the implications `selected_dilation_rate` and
`selected_dilation_not_conserved` (the rate with an arbitrary constant in the hypothesis), the
characterization `stressTrace_eq_zero_iff`, a control on the release's free Maxwell table, and
`det_invariant`: see "The theorems". The limits of scope are listed once, under "What is not
proved".

## How the statements are written

The statements are written with the release's definitions (`YM.*`, and in `PDTAdapters/OnConstructed.lean` and `PDTAdapters/LieDim.lean` the release's root-level `YangMills.*`) and two definitions of this
library: `PDTAdapters.conformal`, the conformal Killing equation, and `PDTAdapters.currentIn`,
the release's formula for the current with the moments read in a second table (equal to the
release's `current` on the own table, by `rfl`). The own-table theorems of
`PDTAdapters/Divergence.lean`, `PDTAdapters/OnFinal.lean` and `PDTAdapters/FreeControl.lean` are
about the release's `current` itself; the per-table, per-phase and selected-phase theorems of
`PDTAdapters/General.lean`, `PDTAdapters/TraceStep.lean`, `PDTAdapters/OnFinal.lean`, `PDTAdapters/OnHeadline.lean`, `PDTAdapters/OnConstructed.lean` and `PDTAdapters/LieDim.lean` are about `currentIn`. No Lean file of the release is modified; how the library is compiled is under "Build".

## Conventions (the release's definitions used)

Euclidean signature, dimension four. Paths are in the release at the commit above.

| declaration (fully qualified) | as written below | where | meaning |
|-------------------------------|------------------|-------|---------|
| `YM.E4`, `YM.Axis` | `E4`, `Axis` | `YM/Space/Configurations.lean`, `YM/Space/Index.lean` | `EuclideanSpace ℝ (Fin 4)` and `Fin 4` |
| `YM.basis` | `basis a` | `YM/Space/Configurations.lean` | the coordinate vector `EuclideanSpace.single a 1` |
| `YM.Analysis.D` | `D u f x` | `YM/Analysis/SmoothJets.lean` | `fderiv ℝ f x u`, the derivative of `f` at `x` in the direction `u` |
| `YM.Points`, `YM.Points.cons`, `YM.Points.tail` | `Points n`, `Points.cons y x`, `Points.tail x` | `YM/Space/Configurations.lean` | `n`-tuples of points of `E4`; the tuple `x` with `y` put in front; the tuple `x` without its first point |
| `YM.conf` | `conf n` | `YM/Space/Configurations.lean` | the configurations of `n` pairwise distinct points |
| `YM.Table.Field`, `YM.Table.Tag`, `YM.Table.unit` | `S.Field d`, `S.Tag`, `S.unit d` | `YM/Euclid/Null.lean`, `YM/Euclid/Lift.lean` | the labels of the table `S` at level `d` (a quotient by the null labels of `S`); a level together with a label at that level; the unit label |
| `YM.Table.useAt` | `S.useAt T x v` | `YM/Euclid/Lift.lean` | the moment of the table `T` at the points `x`, read through the labels `v` of the table `S` |
| `YM.Table.Smooth`, `YM.Table.Symmetric`, `YM.Table.RealSpin` | `S.Smooth`, `S.Symmetric`, `S.RealSpin` | `YM/Euclid/Table.lean` | the moments are `C^∞` on `conf n`; they are unchanged when points and labels are permuted together; the release's reflection and reality laws |
| `YM.Table.respects`, `YM.Table.Hierarchy` | `T.respects S`, `T.Hierarchy` | `YM/Euclid/Lift.lean`, `YM/Euclid/Words.lean` | every null label of `S` is null in `T`; the release's bundle of Euclidean properties of a table (among its fields `laws`, `translations`, `smooth`) |
| `YM.Table.Stress`, `YM.Table.Conserved` | `S.Stress`, `Conserved W H J` | `YM/Euclid/Stress.lean` | `J : Axis → Axis → S.Field 4`; `Conserved` says `J` is symmetric, real, and `∑ a, W.deriv 4 a (J a b) = 0` |
| `YM.DiffPlan`, `YM.DiffPlan.Derivatives` | `DiffPlan S`, `W.Derivatives T` | `YM/Euclid/Differential.lean` | a derivative on labels, and the statement that it realizes the derivative of the moments of `T` |
| `YM.Work.A01.current` | `current J V x q a y` | `YM/Work/A01/Conserve.lean` | `∑ b, V y b • S.useAt S (Points.cons y x) (Fin.cons ⟨4, J a b⟩ q)` |
| `YM.Work.A01.killing` | `killing V` | `YM/Work/A01/Conserve.lean` | `∂_a V_b = −∂_b V_a` |
| `YM.TraceExtension.stressTrace`, `YM.TraceExtension.theta`, `YM.TraceExtension.euclideanVEV` | `stressTrace J`, `theta T J`, `euclideanVEV` | `YM/TraceExtension/Centered.lean` | `∑ i, J i i`; its centred form in the table `T`; the one-point moment |
| `YM.Spec.Materializes`, `YM.Spec.Final`, `YM.Spec.Algebra`, `YM.OS.Selection` | `Spec.Materializes`, `Spec.Final`, `Spec.Algebra`, `OS.Selection` | `YM/Spec/Closed.lean`; `OS.Selection` in `YM/Phase/Mixture.lean` | the release's selection certificate and its final data; the types of the fields `F.sector` and `F.α` of a `Final` |
| `YM.TraceExtension.selected`, `YM.TraceExtension.center`, `YM.TraceExtension.opposed`, `YM.TraceExtension.euclidean` | `selected F`, `center F`, `opposed r`, `euclidean F r` | `YM/TraceExtension/WilsonTrace.lean` | the selected table of a `Spec.Final`; `theta (selected F) F.sector.energy`; a two-point configuration on the time axis at separation `r`; the two-point moment of `center F` at `opposed r` |
| `YM.Table.field_ext`, `YM.Table.at_unit` | `Table.field_ext`, `Table.at_unit` | `YM/Euclid/Lift.lean` | two labels with the same front-slot moments at all separated configurations are equal (for a symmetric table); the unit label in the front slot drops out |
| `YM.Gauge`, `YM.Gauge.Simple`, `YM.Gauge.lieDim`, `YM.Gauge.ad`, `YM.Gauge.Color`, `YM.Gauge.invariant_scalar` | `Gauge`, `G.Simple`, `G.lieDim`, `G.ad`, `G.Color`, `invariant_scalar` | `YM/Gauge/` | the gauge type, simplicity, the dimension of its Lie algebra, the bracket, the colour space; an invariant symmetric bilinear form on the colour space of a simple gauge type is a multiple of the inner product |
| `YM.Labels.Frames`, `YM.Maxwell.freeTable`, `YM.Maxwell.table_smooth` | `Labels.Frames G`, `Maxwell.freeTable F`, `Maxwell.table_smooth F` | `YM/Labels/Basis.lean`, `YM/Euclid/Comparator.lean` | the release's free Maxwell table over a choice of frames `F`, and its smoothness |
| `YM.Maxwell.Free.Model`, `YM.Maxwell.Free.original`, `YM.Maxwell.Free.scheme`, `YM.Maxwell.Free.polStress` | `Maxwell.Free.Model F`, `Maxwell.Free.original F`, `Maxwell.Free.scheme F`, `Maxwell.Free.polStress G` | `YM/Next/MAXWELL/System.lean`, `YM/Next/MAXWELL/Stress.lean` | `freeTable F`; its stress; its derivative plan; the polarized Maxwell stress as a polynomial |
| `YM.Maxwell.Free.Killing` | `Maxwell.Free.Killing v` | `YM/Next/MAXWELL/Current.lean` | for `v : Axis → E4 → ℝ`: smooth components, `∂_a v_b = −∂_b v_a` for `a ≠ b`, and `∂_a v_a = ∂_b v_b` for all `a`, `b` |

Every name in the first column resolves in the environment built for this library. Ten more
names of the release, whose modules are not among the 441 that the build under "Build"
compiles, are cited in this README, besides `YangMills.GaugeGroup`, `YangMills.su2` and
`YangMills.su2Simple`, which are treated at the end of this paragraph: `YM.Trace.Verse.axis_shape` and `YM.Trace.Verse.award`
(`YM/TraceExtension/Verse/Day.lean`), `YM.Nonperturbative.Headline.TraceExclusions`
(`YM/Nonperturbative/HeadlineSpec.lean`), `YangMills.constructed` (`Construction.lean`),
`YM.Trace.trace_free` (`YM/Trace/FreeScalar.lean`), `YM.Trace.rho`
(`YM/TraceExtension/Foundation/Dilate.lean`), `YM.Maxwell.Free.radial_motion` and
`YM.Maxwell.Free.moment_force` (`YM/Next/MAXWELL/Taxes.lean`), and
`YM.EveryPhase.Stress.tide_div` and `YM.EveryPhase.Stress.tensor_conserved` (`YM/EveryPhase/`).
Against the restored compiled build of record 4 of `BUILD.txt`, eight of them resolve in the
environment of `PDTAdapters/OnHeadline.lean` (all but `YM.Trace.trace_free` and
`YangMills.constructed`), and `YM.Trace.trace_free` in a scratch file that imports
`YM.Trace.FreeScalar` (record 4 of `BUILD.txt`, "NAMES"). `YangMills.constructed`, and the
names `YangMills.GaugeGroup`, `YangMills.su2` and `YangMills.su2Simple` used in "On the release's
construction theorem", resolve in the environment of `PDTAdapters/OnConstructed.lean` (record 5).
`YM.Trace.Over.b0`, `YM.Trace.Over.force_b`, `YM.Gauge.casimir_pos`, `YM.Next.Foundations.SUtwo`
and `YangMills.GaugeGroup.coreSimple` resolve in the environment of `PDTAdapters/LieDim.lean` (the
file compiles with them). `YM.Trace.wick_norm`, cited below but not used by the file, resolves in
the same environment (checked by `#check` in a review file importing `PDTAdapters.LieDim`). The
release's `award_eq` (`TraceBridge.lean`) is private and is cited by file and line only;
`YangMills.Hierarchy.TraceTest` (`ChallengeSpec.lean`) and `YangMills.publicTrace`
(`TraceBridge.lean`) are cited by file and line.

Two definitions are added by this library for its statements (two more, the abbreviation `frontCaps` and
the definition `frontIn` in `PDTAdapters/General.lean`, are helpers for the proofs):

- `PDTAdapters.conformal V` (`PDTAdapters/Conformal.lean`): for all `a`, `b`, `x`,
  `∂_a V_b + ∂_b V_a = ½ (∂·V) δ_ab` at `x`, written with the release's `D` and `basis`.
- `PDTAdapters.currentIn T J V x q a y` (`PDTAdapters/General.lean`): the release's `current` with
  the moments read in a second table `T`, that is, with `S.useAt T` in place of `S.useAt S`. At
  `T = S` it is the release's `current` (`currentIn_self`, by `rfl`).

Below, "divergence of the current at `y`" means `∑ a, D (basis a) (current J V x q a) y` (or the
same with `currentIn`), "separated" means `Points.cons y x ∈ conf (n+1)`, and "`V` smooth" means
every coordinate `fun z => V z b` is `ContDiff ℝ ∞`.

## The theorems

All names are in the namespace `PDTAdapters`.

### Stated results

| name | file | statement (all hypotheses) | release definitions it is stated on |
|------|------|----------------------------|-------------------------------------|
| `killing_conformal` | `Conformal.lean` | If `killing V` then `conformal V`. | `killing`, `D`, `basis`, `Axis`, `E4` |
| `dilation_divergence`, `dilation_conformal` | `Conformal.lean` | The field `V(y) = y` has `∑ c, ∂_c V_c = 4` at every point and satisfies `conformal`. | `D`, `basis`, `Axis`, `E4` |
| `conformal_divergence` | `Divergence.lean` | For a table `S` with `S.Smooth`, a `DiffPlan` `W` with `W.Derivatives S`, `H : S.RealSpin`, a stress `J` with `Conserved W H J`, a smooth `V` with `conformal V`, spectator labels `q` at points `x`, and `y` separated from `x`: the divergence of `current J V x q` at `y` equals `((1/4) * ∑ c, ∂_c V_c (y)) • S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q)`. These are the hypotheses of the release's `YM.Work.A01.divergence` with `conformal V` in place of `killing V`. | `Table.Smooth`, `DiffPlan`, `Derivatives`, `RealSpin`, `Stress`, `Conserved`, `current`, `stressTrace`, `useAt`, `conf`, `D` |
| `conformal_divergence_ofReal` | `Divergence.lean` | The same identity with the real factor coerced to `ℂ`. | as above |
| `divergence_of_conformal_killing` | `Divergence.lean` | Under the same hypotheses with `killing V` in place of `conformal V`, the divergence of `current J V x q` at `y` is `0`. The statement is the release's `YM.Work.A01.divergence` (an `example … := rfl` in the file compiles, so the two statements are definitionally equal); here it is derived from `conformal_divergence`. | as above, `killing` |
| `dilation_divergence_trace` | `Divergence.lean` | Under the hypotheses of `conformal_divergence` (without `V`): the divergence of `current J (fun z => z) x q` at `y` equals `S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q)`. | as above |
| `stressTrace_eq_zero_iff` | `Divergence.lean` | For `S` with `S.Symmetric` and `S.Smooth`, `W` with `W.Derivatives S`, and `J` with `Conserved W H J`: `stressTrace J = 0` (equality in the release's `S.Field 4`) if and only if, for every `n`, every `x`, every list of spectator labels `q` and every `y` separated from `x`, the divergence of `current J (fun z => z) x q` at `y` is `0`. `S.Symmetric` is used only for the direction from the divergences to the label (through the release's `Table.field_ext`). | as above, `Table.Symmetric`, `Table.field_ext` |
| `conformal_divergenceIn` | `General.lean` | The identity of `conformal_divergence` with the moments read in a second table `T`: for `T.Smooth`, `W : DiffPlan S` with `W.Derivatives T`, `Conserved W H J`, smooth conformal `V`, and `y` separated from `x`, the divergence of `currentIn T J V x q` at `y` equals `((1/4) * ∑ c, ∂_c V_c (y)) • S.useAt T (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q)`. No `T.respects S` hypothesis is made; see the docstring. | as above with `useAt` at a second table |
| `killing_divergenceIn`, `dilation_divergence_traceIn` | `General.lean` | The Killing case (divergence `0`) and the dilation case (the trace insertion) of `conformal_divergenceIn`, under its hypotheses. | as above, `killing` |
| `phase_conformal_divergence`, `phase_dilation_divergence_trace` | `General.lean` | For `M : Spec.Materializes X Y h` and every index `i` of the selection `Y`: the identity of `conformal_divergenceIn` (for a smooth conformal `V`), and its dilation case, hold in the table `Y.ensemble i` for the stress `X.energy`, at every separated configuration. | `Spec.Materializes`, `Spec.Algebra`, `OS.Selection`, and the above |
| `final_phase_conformal_divergence` | `General.lean` | For `F : Spec.Final C f Z` and every index `i` of `F.α`: the same identity in the table `F.α.ensemble i` for the stress `F.sector.energy`, for a smooth conformal `V`, at every separated configuration. | `Spec.Final`, and the above |
| `det_invariant` | `Det.lean` | For a gauge type `G` with `G.Simple` and an endomorphism `A` of `G.Color` that is symmetric (`A.IsSymmetric`) and satisfies `A (G.ad x y) = G.ad x (A y)` for all `x`, `y`: there is a real `c` with `A = c • 1` and `LinearMap.det A = c ^ G.lieDim`. The scalar clause restates the release's `invariant_scalar` (`YM/Gauge/Casimir.lean`) for endomorphisms, and the determinant clause follows from it at once. `det_invariant` is independent of the other theorems: nothing here uses it, and its file imports only `YM/Gauge/Casimir.lean`. | `Gauge`, `Simple`, `Color`, `ad`, `lieDim`, `invariant_scalar` |
| `dilation_divergence_centerIn` | `TraceStep.lean` | For tables `S`, `T` with `T.respects S` and `T.Hierarchy`, `W : DiffPlan S` with `W.Derivatives T`, `Conserved W H J`, one point `x` and `y ≠ x 0` (`Points.cons y x ∈ conf 2`): the divergence at `y` of `currentIn T J (fun z => z) x` with the single spectator label `theta T J` equals the two-point moment `S.useAt T (Points.cons y x) (fun _ => ⟨4, theta T J⟩)`. | `respects`, `Hierarchy`, `theta`, `useAt`, `Conserved`, `DiffPlan`, `Derivatives`, `conf`, `D` |
| `selected_dilation_divergence`, `selected_dilation_divergence_of_ne` | `TraceStep.lean` | For `F : Spec.Final C f S` and `0 < r` (respectively `r ≠ 0`): the divergence, at the point `opposed r 0`, of `currentIn (selected F) F.sector.energy (fun z => z)` with the spectator label `center F` at the other point of `opposed r` equals `euclidean F r`. | `Spec.Final`, `selected`, `center`, `opposed`, `euclidean` |
| `selected_axis_shape` | `TraceStep.lean` | For `F : Spec.Final C f S` and `x ∈ conf 2`: `S.useAt (selected F) x (fun _ => ⟨4, center F⟩) = euclidean F ‖x 0 - x 1‖`. This is the statement of the release's `YM.Trace.Verse.axis_shape` (`YM/TraceExtension/Verse/Day.lean`) in `useAt` form, re-proved here following the proof text of that declaration because its module is not among those the build under "Build" compiles. It is the release's result, proved here a second time, not a result of this library. The two statements are definitionally equal: the `example … := rfl` in `OnHeadline.lean` compiles (record 4 of `BUILD.txt`). | `Spec.Final`, `selected`, `center`, `euclidean`, `useAt`, `conf` |
| `selected_dilation_divergence_at` | `TraceStep.lean` | For `F : Spec.Final C f S`, one point `x` and `y ≠ x 0`: the divergence at `y` of `currentIn (selected F) F.sector.energy (fun z => z) x` with the spectator label `center F` equals `euclidean F ‖y - x 0‖`. | as above |
| `selected_dilation_rate` | `TraceStep.lean` | For `F : Spec.Final C f S` and a real `c`: IF `(s⁸ (log s⁻¹)²) • euclidean F s → c` as `s → 0⁺`, THEN the same multiple of the divergence of the dilation current at `opposed s` (as in `selected_dilation_divergence`) tends to `c` as `s → 0⁺`. With the release's field `shortDistance` as the hypothesis and `c = Trace.Verse.award G`: `headline_dilation_rate` (`OnHeadline.lean`). | `Spec.Final`, `selected`, `center`, `opposed`, `euclidean` |
| `selected_dilation_not_conserved` | `TraceStep.lean` | Under the same hypothesis and `c ≠ 0`: there is `r₀ > 0` such that the divergence of the dilation current at `opposed r` is nonzero for every `0 < r < r₀`. By `selected_dilation_divergence` this conclusion is the statement `euclidean F r ≠ 0` on `(0, r₀)`. With the release's fields `shortDistance` and `positive` as the hypotheses: `headline_dilation_not_conserved` (`OnHeadline.lean`). | as above |
| `rate_ne_zero`, `rate_zero_control` | `TraceStep.lean` | For any `f : ℝ → ℂ` and real `c ≠ 0`: if `(s⁸ (log s⁻¹)²) • f s → c` as `s → 0⁺` then `f` has no zero on some interval `(0, r₀)`. The control: for `f = 0` and `c = 0` the limit hypothesis holds and the conclusion fails, so `c ≠ 0` cannot be dropped from this step. | none (Mathlib only) |
| `final_conformal_divergence` | `OnFinal.lean` | For `F : Spec.Final C f S`, a smooth `V` with `conformal V`, spectator labels `q` at points `x`, and `y` separated from `x`: the divergence of the release's `current F.sector.energy V x q` at `y` equals `((1/4) * ∑ c, ∂_c V_c (y)) • S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace F.sector.energy⟩ q)`. This is `conformal_divergence` with its hypotheses supplied by `F.room.kernel.smooth`, `F.phase.transport.derivatives` and `F.phase.transport.conserved`. | `Spec.Final`, `current`, `stressTrace`, `useAt`, `conf`, `D` |
| `final_stressTrace_eq_zero_iff` | `OnFinal.lean` | For `F : Spec.Final C f S`: `stressTrace F.sector.energy = 0` if and only if, for every `n`, `x`, `q` and every `y` separated from `x`, the divergence of `current F.sector.energy (fun z => z) x q` at `y` is `0`. This is `stressTrace_eq_zero_iff` with its hypotheses supplied by fields of `F` (`F.room.kernel.laws.toSymmetric` for `S.Symmetric`). | as above |
| `final_phase_dilation_divergence_center` | `OnFinal.lean` | For `F : Spec.Final C f S`, every index `i` of `F.α`, one point `x` and `y ≠ x 0`: with `T = F.α.ensemble i`, the divergence at `y` of `currentIn T F.sector.energy (fun z => z) x` with the single spectator label `theta T F.sector.energy` equals `S.useAt T (Points.cons y x) (fun _ => ⟨4, theta T F.sector.energy⟩)`. This is `dilation_divergence_centerIn` with its hypotheses supplied by `F.phase.phase.retains i`, `F.phase.phase.states i`, `F.phase.phase.calculus i` and `F.phase.transport.conserved`. | `Spec.Final`, `theta`, `useAt`, `conf`, `D` |
| `final_dilation_divergence_center` | `OnFinal.lean` | For `F : Spec.Final C f S`, one point `x` and `y ≠ x 0`: the divergence at `y` of the release's `current F.sector.energy (fun z => z) x` with the single spectator label `theta S F.sector.energy` equals `S.useAt S (Points.cons y x) (fun _ => ⟨4, theta S F.sector.energy⟩)`. This is `dilation_divergence_centerIn` at `T = S`, with `F.room.kernel` for `S.Hierarchy`. | `Spec.Final`, `current`, `theta`, `useAt`, `conf`, `D` |
| `killing_of_conformal`, `killing_iff_conformal` | `OnFinal.lean` | If `conformal V` and `∑ c, ∂_c V_c = 0` at every point, then `killing V`. Hence `killing V` if and only if `conformal V` and `∑ c, ∂_c V_c = 0` at every point (the forward direction is `killing_conformal` with `killing_divergence`). | `killing`, `D`, `basis`, `Axis`, `E4` |
| `conformal_freeKilling` | `OnFinal.lean` | If every coordinate of `V : E4 → E4` is smooth and `conformal V`, then the release's `Maxwell.Free.Killing (fun a x => V x a)` holds. | `Maxwell.Free.Killing`, `D`, `basis` |
| `free_dilation_divergence` | `FreeControl.lean` (not imported by the root) | For `F : Labels.Frames G`, on the release's free-Maxwell table `Maxwell.Free.Model F` with its stress `Maxwell.Free.original F`: at every separated configuration and for every list of spectator labels, the divergence of `current (Maxwell.Free.original F) (fun z => z) x q` at `y` is `0`. The proof uses only `stressTrace (Maxwell.Free.original F) = 0` (`free_stressTrace`). | `Maxwell.Free.Model`, `Maxwell.Free.original`, `Maxwell.Free.scheme`, `Maxwell.table_smooth`, `current`, `stressTrace` |

### Supporting lemmas

| name | file | statement |
|------|------|-----------|
| `killing_diagonal`, `killing_divergence` | `Conformal.lean` | If `killing V` then `∂_a V_a = 0` for each `a`, and `∑ c, ∂_c V_c = 0`. |
| `D_coordinate` | `Conformal.lean` | `D (basis a) (fun y => y b) x` is `1` if `b = a` and `0` otherwise. |
| `contraction` | `Conformal.lean` | For a real array `c` and a symmetric complex array `F` on `Axis × Axis`: if `c a b + c b a` is `½ ∑ e, c e e` for `a = b` and `0` otherwise, then `∑ a b, c a b • F a b = ((1/4) * ∑ e, c e e) • ∑ a, F a a`. |
| `front_trace`, `front_zero` | `Divergence.lean` | The label `stressTrace J` in the front slot of `S.useAt S` reads as the sum of the diagonal insertions; the zero label in the front slot reads `0`. |
| `dilation_smooth` | `Divergence.lean` | The coordinates of `V(y) = y` are smooth. |
| `cons_head_tail` | `Divergence.lean` | `Points.cons (x 0) (Points.tail x) = x`. |
| `currentIn_self` | `General.lean` | `currentIn S J V x q = current J V x q`. |
| `frontIn_eval` | `General.lean` | The front-slot readout `frontIn` (a linear map of the front label, defined in the file) evaluates to `S.useAt T x (Fin.cons ⟨d, p⟩ q)`. |
| `smooth_consIn`, `D_consIn` | `General.lean` | The release's `smooth_cons` and `D_cons` (`YM/Work/A01/Conserve.lean`) with the moments read in a second table `T` (hypotheses `T.Smooth`, `W.Derivatives T`, a separated configuration). The proofs follow the release's. |
| `at_unitIn` | `TraceStep.lean` | For `T.respects S`, `T.Hierarchy` and `x ∈ conf (n+1)`: the unit label `S.unit d` in the front slot of `S.useAt T` drops out. This is the release's `YM.Table.at_unit` (`YM/Euclid/Lift.lean`) with the moments read in a second table; the proof follows the release's. |
| `centered_front` | `TraceStep.lean` | For `T.respects S`, `T.Hierarchy` and `Points.cons y x ∈ conf 2`: against the spectator `theta T J`, the label `stressTrace J` in the front slot of `S.useAt T` reads the same as `theta T J`. |
| `opposed_conf`, `opposed_conf_of_ne` | `TraceStep.lean` | `opposed r ∈ conf 2` for `0 < r`, and for every `r ≠ 0`. |
| `polStress_trace`, `free_stressTrace` | `FreeControl.lean` | The diagonal sum of the release's `Maxwell.Free.polStress G` is `0`; `stressTrace (Maxwell.Free.original F) = 0`. The first is the statement of the release's `YM.Trace.trace_free` (`YM/Trace/FreeScalar.lean`), proved here a second time, with a different proof, because that module is not among those the build under "Build" compiles. It is the release's result. In a scratch file run for record 4 of `BUILD.txt`, against a restored compiled build of the release, `example : @PDTAdapters.polStress_trace = @YM.Trace.trace_free := rfl` compiles: the two statements are definitionally equal (they differ only in whether `G` is explicit). |

The proofs of `conformal_divergence` and `conformal_divergenceIn` follow the release's proof of
`YM.Work.A01.divergence` (`YM/Work/A01/Conserve.lean`) with its last step replaced: after the
Leibniz rule and the vanishing of the term containing the divergence of `J`, the remaining term
pairs the symmetric `J` with `∂V`, and the lemma `contraction` evaluates it with the conformal
equation.

### On the release's `TraceExclusions`

`PDTAdapters/OnHeadline.lean` (not imported by the root). Each theorem takes
`F : Spec.Final C f S` and `H : YM.Nonperturbative.Headline.TraceExclusions F`, the release's
structure in `YM/Nonperturbative/HeadlineSpec.lean`, and uses its fields `shortDistance` (the
limit of `s⁸ (log s⁻¹)² • euclidean F s` as `s → 0⁺` is `Trace.Verse.award G`) and `positive`
(`0 < Trace.Verse.award G`).

| name | statement |
|------|-----------|
| `PDTAdapters.headline_dilation_rate` | `s⁸ (log s⁻¹)²` times the divergence of the dilation current at `opposed s` (as in `selected_dilation_divergence`) tends to `Trace.Verse.award G` as `s → 0⁺`. From `H.shortDistance`, by `selected_dilation_rate`. |
| `PDTAdapters.headline_dilation_not_conserved` | There is `r₀ > 0` such that that divergence at `opposed r` is nonzero for every `0 < r < r₀`. From `H.shortDistance` and `H.positive`, by `selected_dilation_not_conserved`. |
| `PDTAdapters.headline_euclidean_ne_zero` | There is `r₀ > 0` such that `euclidean F r ≠ 0` for every `0 < r < r₀`. From `H.shortDistance` and `H.positive`, by `rate_ne_zero`. |
| `PDTAdapters.headline_dilation_not_conserved_at` | There is `r₀ > 0` such that, for every one-point configuration `x` and every `y` with `y ≠ x 0` and `‖y - x 0‖ < r₀` (the same `r₀` for all `x`), the divergence at `y` of `currentIn (selected F) F.sector.energy (fun z => z) x` with the spectator label `center F` is nonzero. From `headline_euclidean_ne_zero` and `selected_dilation_divergence_at`. |

The module needs the release module `YM.Nonperturbative.HeadlineSpec`, whose import closure is
6,563 of the release's modules; the build under "Build" compiles 441, so it does not check this
module. Record 4 of `BUILD.txt` checks it by compiling this library with `lean -o` against the
public compiled build [`lean-build-3456e5e`](https://github.com/scottnarmstrong/yang-mills-informalization/releases/tag/lean-build-3456e5e) of the release (published by `scottnarmstrong/yang-mills-informalization`, built on Linux x86-64; to obtain it and compile against it, see "The compiled-build route" under "Build"); the limits of that route are under "What is not proved".
`AxiomsOnHeadline.lean` prints the axioms of the four theorems.

### On the release's construction theorem

`PDTAdapters/OnConstructed.lean` (not imported by the root). The release's theorem
`YangMills.constructed` (`Construction.lean`) states, for every simple gauge group `g` and every
`b > 0`, a family `C` and, for every order `p`, a witness `q S F L Q M X` with seventeen clauses,
one of which is `Headline.TraceExclusions F`. The theorems below are universe-polymorphic in the
release's two universes.

| name | statement |
|------|-----------|
| `PDTAdapters.constructed_dilation` | For `g : YangMills.GaugeGroup` with `g.IsSimple`, and `0 < b`: the statement of `YangMills.constructed` (`Construction.lean`, lines 15–31), every clause in the release's order and text, with two conjuncts appended for the same witness `q S F L Q M X`: the conclusion of `headline_dilation_rate` for that `F` (the limit is `Trace.Verse.award g.core`) and the conclusion of `headline_dilation_not_conserved_at` for that `F`. The proof takes the witness of `YangMills.constructed` and applies the two theorems to its clause `Headline.TraceExclusions F`. |
| `PDTAdapters.constructed_dilation_not_conserved` | Under the same hypotheses: there is `C : YM.Family g.core` with penalty `b` and `C.Makes` such that, for every order `p`, there are `q`, `S` and `F : Final C (p.refine q) S` with `Headline.TraceExclusions F` and an `r₀ > 0` such that, for every one-point configuration `x` and every `y ≠ x 0` with `‖y - x 0‖ < r₀`, the divergence at `y` of `currentIn (selected F) F.sector.energy (fun z => z) x` with the spectator label `center F` is nonzero. A projection of `constructed_dilation`. |
| `PDTAdapters.constructed_of_constructed_dilation` | The statement of `YangMills.constructed` at `g hg b hb` (its type is written `type_of%` of that application), derived from `constructed_dilation` by taking its conjuncts apart. Its proof term does not contain `YangMills.constructed` (record 5 lists the constants). So every clause of the release's statement is a conjunct of `constructed_dilation`. |
| `PDTAdapters.su2_dilation_not_conserved` | `constructed_dilation_not_conserved` at the release's `YangMills.su2` (its docstring, `ConcreteSU2.lean` line 7: "The defining complex two-dimensional representation of SU(2)."), with the release's proof `YangMills.su2Simple` of `su2.IsSimple` (both in `ConcreteSU2.lean`), and `b = 1`. It has no hypothesis. |

The module imports `PDTAdapters.OnHeadline` and two of the release's root-level modules:
`Construction`, which holds `YangMills.constructed`, and `ConcreteSU2`, which holds
`YangMills.su2` and `YangMills.su2Simple`. By the import lines of the release's source, the import
closure of `Construction` is 9,456 of the 9,457 modules under `YM/` (all but `YM.Examples.SU2`)
and 10 of the release's 16 root-level Lean files; with `ConcreteSU2` it is all 9,457 modules under
`YM/` and 12 of the 16 root-level files (all but `Challenge`, `Verify`, `VerifyJoint` and `YM`).
The same counts were read in the loaded environment (record 5 of `BUILD.txt`). The build under
"Build" compiles 441 of these modules, so it does not check this module. Record 5 of `BUILD.txt` checks it by compiling it with `lean -o` against the same public compiled build `lean-build-3456e5e` of the release, as in record 4 (limits under "What is not proved"). Loading the environment took about 8 GB of resident memory.
`AxiomsOnConstructed.lean` prints the axioms of the four theorems.

### The constant `Trace.Verse.award` and the dimension of the Lie algebra

`PDTAdapters/LieDim.lean` (not imported by the root; it imports `PDTAdapters.OnConstructed`)
proves that the rate constant of the divergence of the dilation current is three times the
dimension of the gauge Lie algebra over `π⁴`: for every `F` with `Headline.TraceExclusions F`,
and so for the release's construction at every simple gauge group; at the release's SU(2) it is
`9 / π⁴`.

The release defines `YM.Trace.Verse.award G := 12 * (d2 G ^ 2 / b0 G ^ 2) * G.lieDim / π ^ 4`
(`YM/TraceExtension/Verse/Day.lean`, line 41), with `d2 G = -b0 G / 2` (`force_b`) and
`b0 G = 11 * G.casimir / (48 * π ^ 2)` (both in `YM/TraceExtension/Chart/Nectar.lean`).
`G.lieDim` is `Module.finrank ℝ G.Alg` (`YM/Gauge/Colors.lean`, line 41), the dimension over `ℝ`
of the release's Lie algebra `G.lie` of the group (the real subspace of complex matrices `X` with
`exp (t • X)` in the group for every real `t`; `YM/Gauge/Lie.lean`, lines 26 and 126). If `G.casimir ≠ 0`, then `b0 G ≠ 0` and
`award G = 3 * G.lieDim / π ^ 4`; for a simple `G` the Casimir is positive
(`YM.Gauge.casimir_pos`). The release proves this value for `g.core` of a simple
`YangMills.GaugeGroup` as the private theorem `award_eq` (`TraceBridge.lean`, lines 24–33), and
inline in a proof (`YM/TraceExtension/Link/Rad.lean`, lines 98–100). Its public specification
states the same value as the limit of `r⁸ (log r⁻¹)²` times the trace two-point function
`traceTwo` (`ChallengeSpec.lean`, lines 172–174, the structure `Hierarchy.TraceTest`), which the
release's `publicTrace` (`TraceBridge.lean`, line 35) proves from `TraceExclusions`. The value
also appears in the lemma `YM.Trace.wick_norm`
(`YM/TraceExtension/Foundation/Constant.lean`, lines 38–39), for
`quad (Bel L) x (fun _ => fromPol (Bel L) (square4 G))` at two distinct points `x 0 ≠ x 1`, whose
right side at line 39 reads `↑(3*(G.lieDim:ℝ)/Real.pi^4* (‖x 0-x 1‖^8)⁻¹ : ℝ)`. This module
states the value as a public theorem for every `YM.Gauge` with nonzero Casimir, and carries it to
the rate of the divergence of the dilation current (`headline_dilation_rate`).

| name | statement |
|------|-----------|
| `PDTAdapters.award_eq_three_mul_lieDim_of_casimir_ne_zero` | For `G` with `G.casimir ≠ 0`: `Trace.Verse.award G = 3 * G.lieDim / π ^ 4`. |
| `PDTAdapters.award_eq_three_mul_lieDim` | For `G` with `G.Simple`: the same, from the previous theorem by `YM.Gauge.casimir_pos`. |
| `PDTAdapters.award_eq_zero_of_casimir_eq_zero` | A control: if `G.casimir = 0`, then `b0 G = 0` and the release's definition gives `Trace.Verse.award G = 0` (division by zero in `ℝ` is `0`). So the value `3 * G.lieDim / π ^ 4` needs `G.casimir ≠ 0`. No `G` with `G.casimir = 0` and `G.lieDim ≠ 0` is constructed here. |
| `PDTAdapters.headline_dilation_rate_lieDim` | For `H : Headline.TraceExclusions F` (no further hypothesis on `G`: `H.positive` gives `award G ≠ 0`, hence `G.casimir ≠ 0`): `headline_dilation_rate` with the limit written `3 * G.lieDim / π ^ 4`. An `example` in the file checks in the kernel that its statement is that of `headline_dilation_rate` with `Trace.Verse.award G` rewritten by `award_eq_three_mul_lieDim_of_casimir_ne_zero`. |
| `PDTAdapters.constructed_dilation_rate_lieDim` | For `g : YangMills.GaugeGroup` with `g.IsSimple`, and `0 < b`: there is `C : YM.Family g.core` with penalty `b` and `C.Makes` such that, for every order `p`, there are `q`, `S` and `F : Final C (p.refine q) S` with `Headline.TraceExclusions F` and the multiple `s⁸ (log s⁻¹)²` of the divergence of the dilation current at `opposed s` tends to `3 * g.core.lieDim / π ^ 4` as `s → 0⁺`. A projection of `constructed_dilation` (so the witness is that of `YangMills.constructed`), with `award_eq_three_mul_lieDim` at `GaugeGroup.coreSimple hg`. |
| `PDTAdapters.su2_lieDim` | `YangMills.su2.core.lieDim = 3`: the Lie algebra of the release's SU(2) has dimension three. The three matrices of the release's `YM/Examples/SU2.lean` are shown to be a basis; the release's lemmas on them are private, so the file carries copies of them (see `NOTICE`). |
| `PDTAdapters.su2_dilation_rate` | `constructed_dilation_rate_lieDim` at `YangMills.su2`, `YangMills.su2Simple` and `b = 1`, with the limit `9 / π ^ 4`. It has no hypothesis. |

These are consequences of the release's definitions and theorems: the first three are arithmetic
on the definition of `award`, and the others rewrite the limits of `headline_dilation_rate` and
`constructed_dilation` with it. They fill no gap in the release's proof. As with
`PDTAdapters/OnHeadline.lean` and `PDTAdapters/OnConstructed.lean`, the build under "Build" does
not check this module; record 6 of `BUILD.txt` checks it by compiling it with `lean -o` against
the same restored public compiled build `lean-build-3456e5e` of the release: the release's modules
were loaded as compiled, not compiled from source on the machine used, and their declarations
were not re-checked by a kernel replay. Loading the environment took about 8.8 GB of resident
memory. `AxiomsLieDim.lean` prints the axioms of the seven theorems.

## What is not proved

- **The short-distance rate for an `F` not given with `TraceExclusions F`.**
  `selected_dilation_rate` and `selected_dilation_not_conserved` are implications whose
  hypothesis is the release's field `shortDistance` of `TraceExclusions`
  (`YM/Nonperturbative/HeadlineSpec.lean`, lines 93–94; the field is declared at line 92), with an
  arbitrary real constant `c` in place of `Trace.Verse.award G`. This library constructs no
  `F : Spec.Final C f S`. For a given `F`, no theorem here asserts, without the hypothesis
  `TraceExclusions F`, that the trace two-point function, or the divergence of the dilation
  current, is nonzero. For the `F` of the release's `YangMills.constructed` the hypothesis is a
  clause of that theorem (`Construction.lean`, line 28), and the conclusions hold
  (`constructed_dilation`).
- **A from-source check of `OnHeadline.lean`, `OnConstructed.lean` and `LieDim.lean`.** Records 4
  to 6 of `BUILD.txt` compile this library's modules with `lean -o` against the restored public compiled
  build `lean-build-3456e5e` of the release: the release's modules, `HeadlineSpec`,
  `Construction` and `ConcreteSU2` among them, were loaded from the restored files, not compiled
  from source on the machine used, and their declarations were not re-checked by a kernel
  replay. Compiling their import closure from source in the checkout of "Build" would also check
  these three modules and was not done.
- **Anything at coincident points.** Every statement about correlators is made at configurations in `conf`, where all points are distinct: pointwise derivative identities, and limits as `s → 0⁺` and non-vanishing of quantities at such configurations. There is no contact
  term and no distributional extension of the identities across coinciding points.
- **A Ward identity.** None of these statements is a Ward identity, contact or dilation: there is
  no action of the dilation on the inserted fields. The acceptance
  specification in the repository `yang-mills-group/YM` (the file describes itself, at line 18,
  as a proposed specification) says of its own clauses:
  "contact/dilation Ward identities and improvement uniqueness are not clauses"
  ([`submissions/openai-20261028/checks/AcceptanceSpec.lean`](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/AcceptanceSpec.lean),
  line 20, at commit `55ba9fc3`).
- **Improvement uniqueness.** The identities hold for every `J` satisfying `Conserved`; nothing is
  said about which stress is the right one.
- **That `currentIn` is a definition of the release.** In a phase, the current is this library's
  `currentIn`: the release's formula with the moments read in the phase table. On the own table it
  is the release's `current` (`currentIn_self`).
- **That the release's `YM.Maxwell.Free.Killing` implies `conformal`.** That predicate
  (`YM/Next/MAXWELL/Current.lean`) is the conformal Killing equation in components (off-diagonal
  antisymmetry, equal diagonal derivatives) with a smoothness field, on the type `Axis → E4 → ℝ`;
  `conformal` is on `E4 → E4`. `conformal_freeKilling` proves that a `conformal` field with
  smooth components satisfies it; the converse is not formalized here.
- **The dilation about another centre.** The dilation theorems are for the field `V(y) = y`. For
  `V(y) = y − x₀` the identity `conformal_divergence` applies once `conformal V` and smoothness
  are supplied; the library has no lemma that supplies them.
- **That the free-Maxwell stress is nonzero.** `free_dilation_divergence` holds equally for the
  zero stress. It shows that a nonzero divergence does not follow from the definitions `current`,
  `D` and `useAt` alone.

## Relation to a general theorem with Mathlib as its only dependency

The identity of `conformal_divergence` is the form, on the release's correlators, of a standard
identity of flat-space tensor calculus: for a symmetric tensor field `T` and a field `ω`
with `∂_i ω_j + ∂_j ω_i = 2 φ η_ij`,

`div (T·ω) = (div T)·ω + φ · tr_η T`.

That identity is kernel-checked for `ℝⁿ` and any diagonal `η` (statement 6 makes no hypothesis on
`η`), in every dimension, with Mathlib as its only dependency, in the Palomar registry entry
**PALOMAR-2026-11-12-000002**, version 1
(registry record: <https://palomar-registry.org/entry.html?id=PALOMAR-2026-11-12-000002&version=1>;
public repository <https://github.com/stalex444/conformal-killing-flat> at commit
`ef2fbb3488aef70b5e2fbd933c7e01cae6679e48`; statement 6, `div_current_of_conformal`;
statements 7–9 are the two "if and only if" characterizations and the dilation example). With
`η = δ`, `n = 4`, `div T = 0` and `φ = (∂·V)/4` it is the formula proved here.

The two are proved separately. This library does not import that repository (the toolchains
differ: Lean `v4.32.0` here, `v4.35.0-rc2` there), and the statement that the release's correlator
functions `y ↦ S.useAt S (Points.cons y x) (Fin.cons ⟨4, J a b⟩ q)` form a tensor field to which
the general theorem applies is not formalized.

## Related formal work

Described at length, with links at fixed commits and the limits of the search, in the section
"Prior formalization" of the README of the repository named above. In short: the same identity is
formalized for `n = 4`, signature `(1,3)`, for tempered distributions, in `openai/math`
([`lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean`](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean),
`conformal_current_divergence`, at commit `4eaee87548250b2682affda7d05d947c05554bae`). The
release itself has, on the classical free system, a predicate `YM.Maxwell.Free.Killing` that is
the conformal Killing equation in components (its docstring says
that dilation, rotations and translations are admitted; `YM.Maxwell.Free.radial_K` in
`YM/Next/MAXWELL/Affine.lean` is the dilation), and the divergence of the current of its polarized
Maxwell stress for such fields (`YM.Maxwell.Free.current_div`, `YM/Next/MAXWELL/Current.lean`).
On the free system it also has a flux identity for the dilation field with a cutoff
(`YM.Maxwell.Free.radial_flux`, `YM/Next/MAXWELL/Affine.lean`; `YM.Maxwell.Free.radial_motion`
and `YM.Maxwell.Free.moment_force`, `YM/Next/MAXWELL/Taxes.lean`; the module docstrings of the
two files speak of a supplementary dilation charge), and under `YM/TraceExtension` a linear
functional whose docstring calls it the dilation contraction (`YM.Trace.rho`,
`YM/TraceExtension/Foundation/Dilate.lean`). In correlators, the release has the Killing case
for a conserved stress
(`YM.Work.A01.divergence`, `YM/Work/A01/Conserve.lean`). On its analytically continued
correlators it also has the zero-divergence statement for translations and infinitesimal Lorentz
transformations (`YM.EveryPhase.Stress.tide_div`, `YM/EveryPhase/Killing.lean`), and
conservation of the reconstructed stress field (`YM.EveryPhase.Stress.tensor_conserved`,
`YM/EveryPhase/Tensor.lean`). The relation of these to the identities here has not been
examined.
This library proves the conformal Killing case in correlators for a conserved stress, with the
trace term; the release's Killing theorem is its zero-divergence case.

## Build

The library is not a standalone Lake package. The build below compiles it inside a checkout of the release.
Needs Git and elan (the release's `lean-toolchain` selects Lean `v4.32.0`), network access for
`lake exe cache get`, and about 9 GiB of disk. Run on macOS arm64 only; Linux was not tried.

```sh
git clone https://github.com/stalex444/yang-mills-conformal-current.git
git clone https://github.com/yang-mills-group/OpenAI-YM-20261028.git
cd OpenAI-YM-20261028
git checkout 3456e5e75cf8d4cd558955a5c7638fba2d68f464

cp ../yang-mills-conformal-current/PDTAdapters.lean .
cp -R ../yang-mills-conformal-current/PDTAdapters .
cp ../yang-mills-conformal-current/Axioms.lean .     # only for the axiom listing

cat >> lakefile.toml <<'EOF'
[[lean_lib]]
name = "PDTAdapters"
EOF

lake exe cache get                    # Mathlib's compiled files, as in the release's README
lake build PDTAdapters                # the root: Conformal, Divergence, General, Det, TraceStep, OnFinal
lake build PDTAdapters.FreeControl    # built by name; not imported by the root
lake env lean -DmaxHeartbeats=0 -DmaxRecDepth=4096 Axioms.lean    # the axioms of every declaration
```

The two appended lines are the only change to the release; `git status --short` in the checkout
then shows ` M lakefile.toml`, `?? PDTAdapters.lean`, `?? PDTAdapters/`, `?? Axioms.lean` and
`?? .lake/`. Build only these targets: a bare `lake build` would build the release's default
targets, which is a much larger job.

What gets built: by the import lines, 411 of the release's modules for `lake build PDTAdapters`
and 30 more for `PDTAdapters.FreeControl` (441 of the 9,457 files under `YM/`), plus the eight
Lean files of this library other than `PDTAdapters/OnHeadline.lean`,
`PDTAdapters/OnConstructed.lean` and `PDTAdapters/LieDim.lean`, which these targets do not build
(see "On the release's `TraceExclusions`", "On the release's construction theorem" and "The
constant `Trace.Verse.award` and the dimension of the Lie algebra"). `BUILD.txt` holds six
records. Record 1 is a clean-checkout build of
the earlier public commit `41856c2f` (2026-11-13, macOS arm64, 10 cores): the two builds took
4 min 44 s and 57 s and produced 1.1 GiB under `.lake/build`; the dependencies under
`.lake/packages`, with Mathlib's compiled files, take about 7.7 GiB more. Record 2 is the next
commit, `52b2bd2c`, built incrementally in the working checkout of the release (the
clean-checkout run was not repeated); record 3 is the commit after it, which changes Lean
docstrings only, rebuilt the same way. In both, the two targets build with exit code 0 and the axiom listing is
as stated below. Record 4 is the version that adds `PDTAdapters/OnHeadline.lean` and
`AxiomsOnHeadline.lean`: there every module of this library was compiled with `lean -o` against
the restored compiled build of the release, without Lake. Record 5 is the version that adds
`PDTAdapters/OnConstructed.lean` and `AxiomsOnConstructed.lean`, compiled the same way. Record 6
is this version, which adds `PDTAdapters/LieDim.lean` and `AxiomsLieDim.lean`, compiled the same
way.
The files built by the procedure above have not changed since record 3.

The clean-checkout run of record 1 followed these steps with three departures that `BUILD.txt`
states: the files of this library were copied in from a local copy of this repository rather
than from the `git clone` in the first line; the release was cloned from a local clone of its
public repository; and the pinned dependencies came from an existing copy, so the step
`lake exe cache get` was not exercised.

`PDTAdapters.lean` ends with `#print axioms` lines, so `lake build PDTAdapters` prints the axioms
of 34 of the theorems.

### The compiled-build route (`OnHeadline.lean`, `OnConstructed.lean`, `LieDim.lean`)

Records 4 and 5 of `BUILD.txt` compile every module of this library other than `PDTAdapters/LieDim.lean` with `lean -o`, without Lake, and record 6 compiles `PDTAdapters/LieDim.lean` the same way, against the public
compiled build of the release: the GitHub release
[`lean-build-3456e5e`](https://github.com/scottnarmstrong/yang-mills-informalization/releases/tag/lean-build-3456e5e) of
`scottnarmstrong/yang-mills-informalization`. Its archive `ym-build-3456e5e.tgz` is published in two parts with a
`SHA256SUMS` file; the SHA-256 of the joined archive is
`07c145c36a45948ac55044a98d5626c201fe7ad6214d627a0739694c8e464707`. The archive holds the release's `.lake/build`
(paths `./lib/lean/…`, about 8.8 GB unpacked); the records extracted only its 9,470 `.olean` files. The dependencies
are the compiled packages of the checkout of "Build" (`<release>/.lake/packages`, after `lake exe cache get`). This
repository has no `lean-toolchain` file, so Lean `v4.32.0` is named explicitly. From the root of this repository
(compiling `OnConstructed.lean` takes about 9 GB of memory):

```sh
cat ym-build-3456e5e.tgz.part0 ym-build-3456e5e.tgz.part1 > ym-build-3456e5e.tgz
shasum -a 256 -c SHA256SUMS
mkdir <restore> && tar -xzf ym-build-3456e5e.tgz -C <restore>     # <restore>/lib/lean/...

mkdir -p out/PDTAdapters                                          # lean -o does not create directories
P=<release>/.lake/packages
export LEAN_PATH=$PWD/out:<restore>/lib/lean:$P/LeanSearchClient/.lake/build/lib/lean:$P/Qq/.lake/build/lib/lean:$P/aesop/.lake/build/lib/lean:$P/batteries/.lake/build/lib/lean:$P/importGraph/.lake/build/lib/lean:$P/mathlib/.lake/build/lib/lean:$P/plausible/.lake/build/lib/lean:$P/proofwidgets/.lake/build/lib/lean
lean432() { elan run leanprover/lean4:v4.32.0 lean "$@"; }
for m in Conformal Det Divergence General TraceStep OnFinal FreeControl OnHeadline OnConstructed LieDim; do
  lean432 -R . -DmaxHeartbeats=0 -DmaxRecDepth=4096 -o out/PDTAdapters/$m.olean PDTAdapters/$m.lean
done
lean432 -R . -DmaxHeartbeats=0 -DmaxRecDepth=4096 AxiomsOnHeadline.lean      # 4 lines
lean432 -R . -DmaxHeartbeats=0 -DmaxRecDepth=4096 AxiomsOnConstructed.lean   # 4 lines
lean432 -R . -DmaxHeartbeats=0 -DmaxRecDepth=4096 AxiomsLieDim.lean           # 7 lines
```

## Axioms

Every declaration of the seven modules other than `PDTAdapters/OnHeadline.lean`,
`PDTAdapters/OnConstructed.lean` and `PDTAdapters/LieDim.lean` (50 theorems, 3 definitions, 1 abbreviation) depends on
`propext`, `Classical.choice` and `Quot.sound` only (`#print axioms` through `Axioms.lean`; the
54 lines of output are in `BUILD.txt`). The four theorems of `PDTAdapters/OnHeadline.lean`
depend on the same three axioms only (`AxiomsOnHeadline.lean`; record 4 of `BUILD.txt`), and so
do the four theorems of `PDTAdapters/OnConstructed.lean` (`AxiomsOnConstructed.lean`; record 5),
and the seven theorems of `PDTAdapters/LieDim.lean` (`AxiomsLieDim.lean`; record 6).
The source contains no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or
`opaque`.

## Files

| file | content |
|------|---------|
| `PDTAdapters.lean` | root of the library: imports, scope note, `#print axioms` |
| `PDTAdapters/Conformal.lean` | the conformal Killing equation on `E4`; Killing fields and the dilation; the contraction lemma |
| `PDTAdapters/Divergence.lean` | the identity on the own table; the Killing corollary; the dilation case; the trace characterization |
| `PDTAdapters/General.lean` | the identity with moments read in a second table; per phase; in every phase of a `Spec.Final` |
| `PDTAdapters/Det.lean` | invariant symmetric endomorphisms of the colour space |
| `PDTAdapters/TraceStep.lean` | the divergence of the dilation current against the centred trace spectator; the rate in hypothesis form |
| `PDTAdapters/OnFinal.lean` | the identities on the data of a `Spec.Final` (its own table, every phase); `conformal` against the release's `killing` and `Maxwell.Free.Killing` |
| `PDTAdapters/FreeControl.lean` | the free-Maxwell control (not imported by the root) |
| `PDTAdapters/OnHeadline.lean` | the rate statements on the release's `TraceExclusions` (not imported by the root; needs `YM.Nonperturbative.HeadlineSpec`) |
| `PDTAdapters/OnConstructed.lean` | the release's `YangMills.constructed` with the dilation-current clauses for the same witness; the instance at the release's SU(2) (not imported by the root; needs the release's modules `Construction` and `ConcreteSU2`) |
| `PDTAdapters/LieDim.lean` | the release's `Trace.Verse.award` written as `3 * lieDim / π⁴`; the rate statements with that limit; the dimension of the Lie algebra of the release's SU(2) and the rate there (not imported by the root; needs what `OnConstructed.lean` needs) |
| `Axioms.lean` | `#print axioms` for all 54 declarations of the seven modules other than `OnHeadline.lean`, `OnConstructed.lean` and `LieDim.lean`; a check file, not part of the library |
| `AxiomsOnHeadline.lean` | `#print axioms` for the four theorems of `PDTAdapters/OnHeadline.lean`; a check file, not part of the library |
| `AxiomsOnConstructed.lean` | `#print axioms` for the four theorems of `PDTAdapters/OnConstructed.lean`; a check file, not part of the library |
| `AxiomsLieDim.lean` | `#print axioms` for the seven theorems of `PDTAdapters/LieDim.lean`; a check file, not part of the library |
| `LICENSE`, `NOTICE` | the Apache License 2.0; the declarations that follow the release's statements or proof text |
| `.gitignore` | ignores `.lake/` and `.DS_Store` |
| `BUILD.txt`, `SHA256SUMS` | build records (six) and file hashes |

## Provenance and licences

- **The release.** Repository `yang-mills-group/OpenAI-YM-20261028`, commit
  `3456e5e75cf8d4cd558955a5c7638fba2d68f464` (dated 2026-11-05; the only commit in the clone read
  on 2026-11-11). Its `README.md` carries the title Wilson Yang–Mills construction and gives the
  project licence as Apache-2.0; the licence text is its `LICENSE`, and its `NOTICE` and
  `THIRD_PARTY.md` carry the source attributions and the licences of the pinned dependencies.
  That README does not print its own repository's name or commit; both are taken here from the
  clone. The README of `yang-mills-group/YM` (commit `55ba9fc3`) refers to it as the separate
  original-submission repository. This repository contains no file of the release; it copies parts of one, as `NOTICE` lists.
- **This add-on.** Several proofs here follow proof text of the release (`conformal_divergence`
  and `conformal_divergenceIn` up to their last step, `smooth_consIn`, `D_consIn`, `at_unitIn`,
  `selected_axis_shape`, and the one-line `cons_head_tail`); `polStress_trace` proves a
  statement of the release a second time, with a different proof; the statement of
  `constructed_dilation` is the statement text of the release's `YangMills.constructed` with two
  conjuncts appended; `PDTAdapters/LieDim.lean` carries copies of private declarations of the
  release's `YM/Examples/SU2.lean` (namespace `PDTAdapters.SU2Lie`; see `NOTICE`). **Licence of this add-on: the Apache License, Version 2.0 (`LICENSE`),
  the licence of the release; `NOTICE` names the declarations that follow the release's
  statements or proof text.**
- **Author.** Stephanie Alexander (ORCID [0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)).
- **The name.** PDT is Pisot Dimensional Theory, the author's research programme, which derives
  physical constants from two polynomials, x³ − x − 1 (real root ρ) and x⁴ − x − 1 (real root
  Q > 1), with no free parameters. It writes the fine-structure constant as α⁻¹ = (ρQ)¹⁵/π², with
  15 = dim so(4,2), and the ratio of the electron's electromagnetic and gravitational couplings as
  α/α_G = (ρQ)²⁰⁹(2Q − 1)/(π²Q²), with 209 = 15² − 15 − 1
  ([doi:10.5281/zenodo.20417378](https://doi.org/10.5281/zenodo.20417378), §3, Table 2, and §4;
  the ratio follows from the α⁻¹ of Table 2 and the α_G of §4). For the
  gravitational exponent, the programme identifies that 15 with the dimension of the space of
  conformal Killing fields of four-dimensional flat space, the fields that turn every conserved,
  symmetric, trace-free stress tensor into a conserved current (statements 3 and 7 of the
  registered entry PALOMAR-2026-11-12-000002). This library adapts that entry's divergence
  identity for this current (statement 6) to the definitions of the Yang–Mills release.
- **Agent assistance.** The Lean proofs and this README were written by Claude (Anthropic) agent
  sessions in Claude Code, directed by the author. Every theorem is checked by the Lean kernel,
  and each statement was reviewed by a separate agent session that had not written it. The author
  read the theorem statements before publication. No other model was used. The
  evidence offered is what can be re-run: the builds and
  axiom listing in `BUILD.txt`, the `example … := rfl` in `PDTAdapters/Divergence.lean`, and the
  control `rate_zero_control`. The builds recorded in `BUILD.txt` were run on the author's
  machine.
