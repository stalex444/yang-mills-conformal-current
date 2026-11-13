# PDTAdapters: the divergence of the stress current against conformal Killing fields, on the definitions of the Wilson Yang–Mills release

An add-on Lean library for the Lean source distribution of the Wilson Yang–Mills construction in
the repository
[`yang-mills-group/OpenAI-YM-20261028`](https://github.com/yang-mills-group/OpenAI-YM-20261028/tree/3456e5e75cf8d4cd558955a5c7638fba2d68f464),
commit `3456e5e75cf8d4cd558955a5c7638fba2d68f464` ("the release" below; Lean `v4.32.0`, Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`).

The library contains kernel-checked theorems about the divergence of the release's stress
current against conformal Killing fields and against the dilation field. The statements are
written with the release's definitions (`YM.*`) and two definitions of this library:
`PDTAdapters.conformal`, the conformal Killing equation, and `PDTAdapters.currentIn`, the
release's formula for the current with the moments read in a second table (equal to the release's
`current` on the own table, by `rfl`). The own-table theorems of `PDTAdapters/Divergence.lean`
and `PDTAdapters/FreeControl.lean` are about the release's `current` itself; the per-table,
per-phase and selected-phase theorems of `PDTAdapters/General.lean` and
`PDTAdapters/TraceStep.lean` are about `currentIn`. The library is compiled inside a copy of the
release and no file of the release is modified.

In one sentence: under the hypotheses of the release's theorem `YM.Work.A01.divergence` (a smooth
table, a derivative plan realizing its derivatives, a conserved stress `J` in the release's
sense, a field `V` smooth in each coordinate), with the conformal Killing equation on Euclidean
`ℝ⁴` in place of the Killing equation, the divergence of the release's `current J V` in
correlators, at configurations with all points distinct, equals `(∂·V)/4` times the correlator
with the trace label `stressTrace J` inserted. The release's theorem `YM.Work.A01.divergence`
(Killing fields, divergence zero) is the case `∂·V = 0`, and for the dilation field `V(y) = y`
the divergence is the trace insertion itself.

All statements are at **separated points** (configurations in the release's `conf`). The
short-distance rate statements are in **hypothesis form**. See "What is not proved".

## Conventions (the release's definitions used)

Euclidean signature, dimension four. Paths are in the release at the commit above.

| name | where | meaning |
|------|-------|---------|
| `E4`, `Axis` | `YM/Space/Configurations.lean`, `YM/Space/Index.lean` | `EuclideanSpace ℝ (Fin 4)` and `Fin 4` |
| `D u f x` | `YM/Analysis/SmoothJets.lean` | `fderiv ℝ f x u`, the derivative of `f` at `x` in the direction `u` |
| `conf n` | `YM/Space/Configurations.lean` | the configurations of `n` pairwise distinct points |
| `S.useAt T x v` | `YM/Euclid/Lift.lean` | the moment of the table `T` at the points `x`, read through the labels `v` of the table `S` |
| `S.Stress`, `Conserved W H J` | `YM/Euclid/Stress.lean` | `J : Axis → Axis → S.Field 4`; `Conserved` says `J` is symmetric, real, and `∑ a, W.deriv 4 a (J a b) = 0` |
| `DiffPlan S`, `W.Derivatives T` | `YM/Euclid/Differential.lean` | a derivative on labels, and the statement that it realizes the derivative of the moments of `T` |
| `current J V x q a y` | `YM/Work/A01/Conserve.lean` | `∑ b, V y b • S.useAt S (Points.cons y x) (Fin.cons ⟨4, J a b⟩ q)` |
| `killing V` | `YM/Work/A01/Conserve.lean` | `∂_a V_b = −∂_b V_a` |
| `stressTrace J`, `theta T J`, `euclideanVEV` | `YM/TraceExtension/Centered.lean` | `∑ i, J i i`; its centred form in the table `T`; the one-point moment |
| `Spec.Materializes`, `Spec.Final` | `YM/Spec/Closed.lean` | the release's selection certificate and its final data |
| `selected F`, `center F`, `opposed r`, `euclidean F r` | `YM/TraceExtension/WilsonTrace.lean` | the selected table of a `Spec.Final`; `theta (selected F) F.sector.energy`; a two-point configuration on the time axis at separation `r`; the two-point moment of `center F` at `opposed r` |
| `Gauge`, `G.Simple`, `G.lieDim`, `G.ad`, `G.Color` | `YM/Gauge/` | the gauge type, simplicity, the dimension of its Lie algebra, the bracket, the colour space |

Two definitions are added by this library for its statements (two more, `frontCaps` and
`frontIn` in `PDTAdapters/General.lean`, are helpers for the proofs):

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
| `det_invariant` | `Det.lean` | For a gauge type `G` with `G.Simple` and an endomorphism `A` of `G.Color` that is symmetric (`A.IsSymmetric`) and satisfies `A (G.ad x y) = G.ad x (A y)` for all `x`, `y`: there is a real `c` with `A = c • 1` and `LinearMap.det A = c ^ G.lieDim`. Derived from the release's `invariant_scalar` (`YM/Gauge/Casimir.lean`). | `Gauge`, `Simple`, `Color`, `ad`, `lieDim`, `invariant_scalar` |
| `dilation_divergence_centerIn` | `TraceStep.lean` | For tables `S`, `T` with `T.respects S` and `T.Hierarchy`, `W : DiffPlan S` with `W.Derivatives T`, `Conserved W H J`, one point `x` and `y ≠ x 0` (`Points.cons y x ∈ conf 2`): the divergence at `y` of `currentIn T J (fun z => z) x` with the single spectator label `theta T J` equals the two-point moment `S.useAt T (Points.cons y x) (fun _ => ⟨4, theta T J⟩)`. | `respects`, `Hierarchy`, `theta`, `useAt`, `Conserved`, `DiffPlan`, `Derivatives`, `conf`, `D` |
| `selected_dilation_divergence`, `selected_dilation_divergence_of_ne` | `TraceStep.lean` | For `F : Spec.Final C f S` and `0 < r` (respectively `r ≠ 0`): the divergence, at the point `opposed r 0`, of `currentIn (selected F) F.sector.energy (fun z => z)` with the spectator label `center F` at the other point of `opposed r` equals `euclidean F r`. | `Spec.Final`, `selected`, `center`, `opposed`, `euclidean` |
| `selected_axis_shape` | `TraceStep.lean` | For `F : Spec.Final C f S` and `x ∈ conf 2`: `S.useAt (selected F) x (fun _ => ⟨4, center F⟩) = euclidean F ‖x 0 - x 1‖`. This is the statement of the release's `YM.Trace.Verse.axis_shape` (`YM/TraceExtension/Verse/Day.lean`) in `useAt` form, re-proved here following the proof text of that declaration because its module is not among those built for this library. It is the release's result, proved here a second time, not a result of this library. | `Spec.Final`, `selected`, `center`, `euclidean`, `useAt`, `conf` |
| `selected_dilation_divergence_at` | `TraceStep.lean` | For `F : Spec.Final C f S`, one point `x` and `y ≠ x 0`: the divergence at `y` of `currentIn (selected F) F.sector.energy (fun z => z) x` with the spectator label `center F` equals `euclidean F ‖y - x 0‖`. | as above |
| `selected_dilation_rate` | `TraceStep.lean` | **Hypothesis form.** For `F : Spec.Final C f S` and a real `c`: IF `(s⁸ (log s⁻¹)²) • euclidean F s → c` as `s → 0⁺`, THEN the same multiple of the divergence of the dilation current at `opposed s` (as in `selected_dilation_divergence`) tends to `c` as `s → 0⁺`. | `Spec.Final`, `selected`, `center`, `opposed`, `euclidean` |
| `selected_dilation_not_conserved` | `TraceStep.lean` | **Hypothesis form.** Under the same hypothesis and `c ≠ 0`: there is `r₀ > 0` such that the divergence of the dilation current at `opposed r` is nonzero for every `0 < r < r₀`. By `selected_dilation_divergence` this conclusion is the statement `euclidean F r ≠ 0` on `(0, r₀)`. The name describes the conclusion; the theorem is an implication. | as above |
| `rate_ne_zero`, `rate_zero_control` | `TraceStep.lean` | For any `f : ℝ → ℂ` and real `c ≠ 0`: if `(s⁸ (log s⁻¹)²) • f s → c` as `s → 0⁺` then `f` has no zero on some interval `(0, r₀)`. The control: for `f = 0` and `c = 0` the limit hypothesis holds and the conclusion fails, so `c ≠ 0` cannot be dropped from this step. | none (Mathlib only) |
| `free_dilation_divergence` | `FreeControl.lean` (not imported by the root) | For `F : Labels.Frames G`, on the release's free-Maxwell table `Maxwell.Free.Model F` with its stress `Maxwell.Free.original F`: at every separated configuration and for every list of spectator labels, the divergence of `current (Maxwell.Free.original F) (fun z => z) x q` at `y` is `0`. The proof uses only `stressTrace (Maxwell.Free.original F) = 0` (`free_stressTrace`); the file does not prove that this stress is nonzero. | `Maxwell.Free.Model`, `Maxwell.Free.original`, `Maxwell.Free.scheme`, `Maxwell.table_smooth`, `current`, `stressTrace` |

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
| `at_unitIn` | `TraceStep.lean` | For `T.respects S`, `T.Hierarchy` and `x ∈ conf (n+1)`: the unit label `S.unit d` in the front slot of `S.useAt T` drops out. |
| `centered_front` | `TraceStep.lean` | For `T.respects S`, `T.Hierarchy` and `Points.cons y x ∈ conf 2`: against the spectator `theta T J`, the label `stressTrace J` in the front slot of `S.useAt T` reads the same as `theta T J`. |
| `opposed_conf`, `opposed_conf_of_ne` | `TraceStep.lean` | `opposed r ∈ conf 2` for `0 < r`, and for every `r ≠ 0`. |
| `polStress_trace`, `free_stressTrace` | `FreeControl.lean` | The diagonal sum of the release's `Maxwell.Free.polStress G` is `0`; `stressTrace (Maxwell.Free.original F) = 0`. |

The proofs of `conformal_divergence` and `conformal_divergenceIn` follow the release's proof of
`YM.Work.A01.divergence` (`YM/Work/A01/Conserve.lean`) with its last step replaced: after the
Leibniz rule and the vanishing of the term containing the divergence of `J`, the remaining term
pairs the symmetric `J` with `∂V`, and the lemma `contraction` evaluates it with the conformal
equation.

## What is not proved

- **The unconditional short-distance rate.** `selected_dilation_rate` and
  `selected_dilation_not_conserved` are implications. Their hypothesis is the limit statement that
  the release writes as the field `shortDistance` of its structure `TraceExclusions`
  (`YM/Nonperturbative/HeadlineSpec.lean`, lines 92–94), with an arbitrary real constant `c` in
  place of the release's constant `Trace.Verse.award G`. This library does not prove that
  hypothesis for any `F`, and it constructs no `F : Spec.Final C f S`. Discharging the hypothesis
  from the release's own theorem needs modules of the release that were not built for this
  library (the import closure of `YM/Nonperturbative/HeadlineSpec.lean` is 6,563 of the release's
  modules; 441 were built here), so the one-line application of these two theorems to the
  release's `shortDistance` and `positive` fields has not been compiled. No theorem here asserts
  that the trace two-point function, or the divergence of the dilation current, of the constructed
  theory is nonzero.
- **Anything at coincident points.** Every statement is a pointwise derivative identity for
  correlators at configurations in `conf`, where all points are distinct.
- **A Ward identity.** None of these statements is a Ward identity, contact or dilation: there are
  no coincident-point terms and no action of the dilation on the inserted fields. The acceptance
  specification in the repository `yang-mills-group/YM` (the file describes itself, at line 18,
  as a proposed specification) says of its own clauses:
  "contact/dilation Ward identities and improvement uniqueness are not clauses"
  ([`submissions/openai-20261028/checks/AcceptanceSpec.lean`](https://github.com/yang-mills-group/YM/blob/55ba9fc36293b3f4d52c6b1f813169a0be76ee98/submissions/openai-20261028/checks/AcceptanceSpec.lean),
  lines 19–20, at commit `55ba9fc3`). No statement here is offered as one of those identities.
- **A contact term**, or any distributional extension of the identities across coinciding points.
- **Improvement uniqueness.** The identities hold for every `J` satisfying `Conserved`; nothing is
  said about which stress is the right one.
- **That `currentIn` is a definition of the release.** In a phase, the current is this library's
  `currentIn`: the release's formula with the moments read in the phase table. On the own table it
  is the release's `current` (`currentIn_self`).
- **That `conformal` is the release's `YM.Maxwell.Free.Killing`.** That predicate
  (`YM/Next/MAXWELL/Current.lean`) is the conformal Killing equation in components (off-diagonal
  antisymmetry, equal diagonal derivatives) with a smoothness field, on the type `Axis → E4 → ℝ`;
  `conformal` is on `E4 → E4`. Their equivalence is not formalized here.
- **The dilation about another centre.** The dilation theorems are for the field `V(y) = y`. For
  `V(y) = y − x₀` the identity `conformal_divergence` applies once `conformal V` and smoothness
  are supplied; the library has no lemma that supplies them.
- **That the free-Maxwell stress is nonzero.** `free_dilation_divergence` holds equally for the
  zero stress. It shows that a nonzero divergence does not follow from the definitions `current`,
  `D` and `useAt` alone; it is not presented as a contrast between two theories.
- `det_invariant` is about symmetric endomorphisms only; it is not a statement about every
  operator commuting with the adjoint action.

## Relation to a general theorem in Mathlib alone

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
(`lean/OAI/Analysis/TemperedDistribution/ConformalIdentities.lean`,
`conformal_current_divergence`). The release itself has, on the classical free system, a predicate
`YM.Maxwell.Free.Killing` that is the conformal Killing equation in components (its docstring says
that dilation, rotations and translations are admitted; `radial_K` in
`YM/Next/MAXWELL/Affine.lean` is the dilation), and the divergence of the current of its polarized
Maxwell stress for such fields (`YM/Next/MAXWELL/Current.lean`, `current_div`); and, in
correlators, the Killing case for a conserved stress (`YM/Work/A01/Conserve.lean`, `divergence`).
This library proves the conformal Killing case in correlators for a conserved stress, with the
trace term; the release's Killing theorem is its zero-divergence case. No claim of priority is
made for anything in this repository.

## Build

The library is not a standalone Lake package. It is compiled inside a checkout of the release.

```sh
git clone https://github.com/yang-mills-group/OpenAI-YM-20261028.git
cd OpenAI-YM-20261028
git checkout 3456e5e75cf8d4cd558955a5c7638fba2d68f464

# copy PDTAdapters.lean and the directory PDTAdapters/ from this repository into the checkout

cat >> lakefile.toml <<'EOF'
[[lean_lib]]
name = "PDTAdapters"
EOF

lake exe cache get                    # Mathlib's compiled files, as in the release's README
lake build PDTAdapters                # the root: Conformal, Divergence, General, Det, TraceStep
lake build PDTAdapters.FreeControl    # built by name; not imported by the root
```

The two appended lines are the only change to the release; `git status --short` in the checkout
then shows ` M lakefile.toml`, `?? PDTAdapters.lean`, `?? PDTAdapters/` (and `?? .lake/`, and
`?? Axioms.lean` if that file is copied in). Build only these targets: a bare `lake build` would
build the release's default targets, which is a much larger job.

What gets built: 406 of the release's modules for `lake build PDTAdapters` and 35 more for
`PDTAdapters.FreeControl` (441 of the 9,457 files under `YM/`), plus the seven files of this
library. In the run recorded in `BUILD.txt` (2026-11-13, a clean checkout, macOS arm64, 10
cores) the two builds took 4 min 44 s and 57 s and produced 1.1 GiB under `.lake/build`; the
dependencies under `.lake/packages`, with Mathlib's compiled files, take about 7.7 GiB more.

Tested as written except for two things that `BUILD.txt` states: the clone was made from a
local clone of the public repository, and the pinned dependencies came from an existing copy, so
the step `lake exe cache get` was not exercised.

To print the axioms of every declaration, copy `Axioms.lean` into the checkout as well and run
`lake env lean -DmaxHeartbeats=0 -DmaxRecDepth=4096 Axioms.lean` after the two builds.

`PDTAdapters.lean` ends with `#print axioms` lines, so `lake build PDTAdapters` prints the axioms
of 27 of the theorems.

## Axioms

Every declaration of the six modules (43 theorems and 4 definitions) depends on `propext`,
`Classical.choice` and `Quot.sound` only (`#print axioms` through `Axioms.lean`; the 47 lines of
output are in `BUILD.txt`). The source
contains no `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `opaque`.

## Files

| file | content |
|------|---------|
| `PDTAdapters.lean` | root of the library: imports, scope note, `#print axioms` |
| `PDTAdapters/Conformal.lean` | the conformal Killing equation on `E4`; Killing fields and the dilation; the contraction lemma |
| `PDTAdapters/Divergence.lean` | the identity on the own table; the Killing corollary; the dilation case; the trace characterization |
| `PDTAdapters/General.lean` | the identity with moments read in a second table; per phase; on a `Spec.Final` |
| `PDTAdapters/Det.lean` | invariant symmetric endomorphisms of the colour space |
| `PDTAdapters/TraceStep.lean` | the divergence of the dilation current against the centred trace spectator; the rate in hypothesis form |
| `PDTAdapters/FreeControl.lean` | the free-Maxwell control (not imported by the root) |
| `Axioms.lean` | `#print axioms` for all 47 declarations; a check file, not part of the library |
| `BUILD.txt`, `SHA256SUMS` | build record and file hashes |

## Provenance and licences

- **The release.** Repository `yang-mills-group/OpenAI-YM-20261028`, commit
  `3456e5e75cf8d4cd558955a5c7638fba2d68f464` (dated 2026-11-05; the only commit in the clone read
  on 2026-11-11). Its `README.md` carries the title Wilson Yang–Mills construction and gives the
  project licence as Apache-2.0; the licence text is its `LICENSE`, and its `NOTICE` and
  `THIRD_PARTY.md` carry the source attributions and the licences of the pinned dependencies.
  That README does not print the repository's name or a commit; both are taken here from the
  clone. The README of `yang-mills-group/YM` (commit `55ba9fc3`) refers to it as the separate
  original-submission repository. This repository contains no file of the release.
- **This add-on.** Several proofs here follow proof text of the release, as stated above
  (`conformal_divergence`, `conformal_divergenceIn`, `smooth_consIn`, `D_consIn`,
  `selected_axis_shape`). **Licence of this add-on: the Apache License,
  Version 2.0 (`LICENSE`), the licence of the release; `NOTICE` names the passages that follow
  the release's proof text.**
- **Author.** Stephanie Alexander (ORCID [0009-0003-7727-2565](https://orcid.org/0009-0003-7727-2565)).
- Developed with AI assistance (Anthropic Claude, in Claude Code) under the author's direction.
  The builds recorded in `BUILD.txt` were run on the author's machine. Statement reviews by
  separate AI sessions (hypothesis deletion, vacuity checks, comparison of the rate hypothesis
  with the release's text) were made during development; their records are not part of this
  repository.
