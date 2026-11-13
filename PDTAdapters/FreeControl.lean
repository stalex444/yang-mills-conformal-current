import PDTAdapters.Divergence
import YM.Next.MAXWELL.System

/-!
# Control: the dilation current of `Free.original F` on `freeTable F`

On the release's table `YM.Maxwell.freeTable F` (`Maxwell.Free.Model F`), with its conserved stress
`Maxwell.Free.original F`, the trace label `stressTrace (Maxwell.Free.original F)` is zero, and so
the dilation current is divergence-free at every separated configuration, with every list of
spectator tags.

This is a statement on a different table from the one in `PDTAdapters.TraceStep`, with the
own-table `current`. The proof uses only `stressTrace (Maxwell.Free.original F) = 0`: the same
conclusion holds for every conserved stress whose trace label is zero, the zero stress included,
and this file does not prove that `Maxwell.Free.original F` is nonzero. It shows that a nonzero
divergence is not a consequence of the definitions `current`, `D` and `useAt` alone.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01 YM.TraceExtension
open scoped BigOperators ContDiff

variable {G : Gauge}

/-- The diagonal sum of the release's `polStress` is zero. -/
theorem polStress_trace (G : Gauge) : ∑ a : Axis, Maxwell.Free.polStress G a a = 0 := by
  unfold Maxwell.Free.polStress
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  simp [Maxwell.Free.kr_eq]

/-- The trace label of `Maxwell.Free.original F` is zero. -/
theorem free_stressTrace (F : Labels.Frames G) : stressTrace (Maxwell.Free.original F) = 0 := by
  apply Maxwell.Free.address_inj F 4
  rw [stressTrace, map_sum, map_zero]
  simp_rw [Maxwell.Free.inertia]
  exact polStress_trace G

/-- **Control.** The dilation current of `Free.original F` on `freeTable F` is divergence-free at
every separated configuration. -/
theorem free_dilation_divergence (F : Labels.Frames G) {n} {x : Points n}
    (q : Fin n → (Maxwell.Free.Model F).Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current (Maxwell.Free.original F) (fun z : E4 => z) x q a) y = 0 := by
  rw [dilation_divergence_trace (Maxwell.table_smooth F) (Maxwell.Free.scheme F)
    (Maxwell.Free.scheme_derives F) (Maxwell.Free.original F) (Maxwell.Free.realStress F) q hy,
    free_stressTrace, front_zero]

end PDTAdapters
