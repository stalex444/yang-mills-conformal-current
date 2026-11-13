import PDTAdapters.OnHeadline
import Construction
import ConcreteSU2

/-!
# The release's construction theorem with the dilation-current clauses

The release's theorem `YangMills.constructed` (`Construction.lean`) states, for every simple
gauge group `g` and every `b > 0`, a family `C` and, for every order `p`, a witness
`q S F L Q M X` with seventeen clauses, one of which is `Headline.TraceExclusions F`. This file
adds to that witness the conclusions of two theorems of `PDTAdapters/OnHeadline.lean`, applied to
that clause.

* `constructed_dilation` — the statement of `YangMills.constructed`, with its clauses in the
  release's order and in the release's terms, and two more conjuncts for the same
  `q S F L Q M X`: the conclusion of `headline_dilation_rate` for that `F` (the multiple
  `s⁸ (log s⁻¹)²` of the divergence of the dilation current at `opposed s` tends to
  `Trace.Verse.award g.core` as `s → 0⁺`) and the conclusion of
  `headline_dilation_not_conserved_at` for that `F` (there is `r₀ > 0` such that the divergence
  at `y` of the dilation current against the spectator `center F` at `x` is nonzero for every
  `y ≠ x 0` with `‖y - x 0‖ < r₀`).
* `constructed_dilation_not_conserved` — the short form: the family `C` with its penalty `b` and
  `C.Makes`, and for every order `p` a table `S` and an `F` with `Headline.TraceExclusions F` and
  the second of the two conclusions.
* `constructed_of_constructed_dilation` — the statement of `YangMills.constructed` at
  `g hg b hb`, derived from `constructed_dilation` by taking its conjuncts apart; the proof does
  not use `YangMills.constructed`.
* `su2_dilation_not_conserved` — `constructed_dilation_not_conserved` at the release's
  `YangMills.su2` and `YangMills.su2Simple` (`ConcreteSU2.lean`) and `b = 1`.

The hypotheses of `constructed_dilation`, `constructed_dilation_not_conserved` and
`constructed_of_constructed_dilation` are those of `YangMills.constructed`: `g.IsSimple` and
`0 < b`. `su2_dilation_not_conserved` has none.
Checked against the restored public compiled build of the release; see `BUILD.txt` record 5.
Nothing here concerns coincident points.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YangMills YM YM.Spec YM.OPE.Orbits YM.Nonperturbative
open YM.Table YM.Analysis YM.TraceExtension Filter
open scoped BigOperators Topology

universe u v

/-- **The release's construction theorem with the dilation-current clauses.** For every simple
`g` and every `b > 0`: the statement of the release's `YangMills.constructed`, every clause in
the release's order and terms, with two conjuncts appended for the same witness
`q S F L Q M X`: the conclusion of `headline_dilation_rate` and the conclusion of
`headline_dilation_not_conserved_at` for that `F`. The proof takes the witness from
`YangMills.constructed` and applies the two theorems to its clause
`Headline.TraceExclusions F`. -/
theorem constructed_dilation (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ) (hb : 0 < b) :
    ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
      WilsonRegularity (wilsonFamily C) ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S) (L : EveryPhase.Almanac F)
        (Q : Reader F.sector.derivatives F.sector.turns F.room.kernel.spin)
        (M : Contacts.Devices F.sector.derivatives) (X : Climb.Scaling S),
        (hierarchy F Q).Properties (p.refine q).per ∧ (hierarchy F Q).Contacts ∧
        (Extraction.Order.mk Extraction.Sequence.full (p.refine q).per).Ordered C S ∧
        FullVolume.PositionsUV C Extraction.Sequence.full ∧ Spec.Calibrated C ∧
        Independent.Core.{u,v} (GaugeGroup.coreSimple hg) F L Q ∧
        Headline.Reconstruction F L ∧
        (∀ i, (view (L.actors i)).Axioms) ∧
        Headline.SeparatedOPE F Q ∧ Headline.NestedOPE F Q ∧ Headline.TraceExclusions.{u,v} F ∧
        M.basis = Q.port ∧ Contacts.Solstice.MultipleLight F M ∧
        Nonempty (Contacts.Transport.SystemBasis M) ∧ Nonempty (Contacts.Solstice.Thresholds M) ∧
        Pert.FirstExtension F X ∧ Pert.Position.FourMeters F X ∧
        Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
            ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
              (YM.Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a)
              (opposed s 0))
          (𝓝[>] 0) (𝓝 (Trace.Verse.award g.core : ℂ)) ∧
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (x : YM.Points 1) (y : E4), y ≠ x 0 → ‖y - x 0‖ < r₀ →
          ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z) x
            (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) y ≠ 0 := by
  obtain ⟨C, penalty, makes, regular, orders⟩ := YangMills.constructed.{u,v} g hg b hb
  refine ⟨C, penalty, makes, regular, fun p => ?_⟩
  obtain ⟨q, S, F, L, Q, M, X, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, trace, c12, c13, c14,
    c15, c16, c17⟩ := orders p
  exact ⟨q, S, F, L, Q, M, X, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, trace, c12, c13, c14,
    c15, c16, c17, headline_dilation_rate F trace, headline_dilation_not_conserved_at F trace⟩

/-- **Non-conservation of the dilation current, for the release's construction.** For every
simple `g` and every `b > 0` there is a family `C` with penalty `b` and `C.Makes` such that, for
every order `p`, there are `q`, a table `S` and `F : Final C (p.refine q) S` with
`Headline.TraceExclusions F` and a radius `r₀ > 0` such that, for every one-point configuration
`x` and every `y ≠ x 0` with `‖y - x 0‖ < r₀`, the divergence at `y` of the dilation current of
`F.sector.energy`, read in `selected F` against the spectator `center F` at `x`, is nonzero.
The proof projects `constructed_dilation`; the witness is that of `YangMills.constructed`. -/
theorem constructed_dilation_not_conserved (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ)
    (hb : 0 < b) :
    ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S), Headline.TraceExclusions.{u,v} F ∧
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (x : YM.Points 1) (y : E4), y ≠ x 0 → ‖y - x 0‖ < r₀ →
          ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z) x
            (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) y ≠ 0 := by
  obtain ⟨C, penalty, makes, -, orders⟩ := constructed_dilation.{u,v} g hg b hb
  refine ⟨C, penalty, makes, fun p => ?_⟩
  obtain ⟨q, S, F, -, -, -, -, -, -, -, -, -, -, -, -, -, -, trace, -, -, -, -, -, -, -,
    notConserved⟩ := orders p
  exact ⟨q, S, F, trace, notConserved⟩

/-- **Nothing dropped or altered.** The statement of the release's `YangMills.constructed` at
`g hg b hb` (the type is written `type_of%` of that application), derived from
`constructed_dilation` by taking its conjuncts apart and leaving out the two appended ones. The
proof does not use `YangMills.constructed` (see `BUILD.txt` record 5 for the constants of the
proof term). -/
theorem constructed_of_constructed_dilation (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ)
    (hb : 0 < b) : type_of% (YangMills.constructed.{u,v} g hg b hb) := by
  obtain ⟨C, penalty, makes, regular, orders⟩ := constructed_dilation.{u,v} g hg b hb
  refine ⟨C, penalty, makes, regular, fun p => ?_⟩
  obtain ⟨q, S, F, L, Q, M, X, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17, -, -⟩ := orders p
  exact ⟨q, S, F, L, Q, M, X, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14,
    c15, c16, c17⟩

/-- **At the release's SU(2).** `constructed_dilation_not_conserved` at the release's gauge
group `YangMills.su2` with the release's proof `YangMills.su2Simple` of its simplicity
(`ConcreteSU2.lean`) and `b = 1`. -/
theorem su2_dilation_not_conserved :
    ∃ C : YM.Family su2.core, C.path.levels.clock.kernel.penalty = 1 ∧ C.Makes ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S), Headline.TraceExclusions.{u,v} F ∧
        ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ (x : YM.Points 1) (y : E4), y ≠ x 0 → ‖y - x 0‖ < r₀ →
          ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z) x
            (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a) y ≠ 0 :=
  constructed_dilation_not_conserved.{u,v} su2 su2Simple 1 one_pos

end PDTAdapters
