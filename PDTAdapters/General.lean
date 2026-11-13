import YM.Work.A01.Conserve
import YM.TraceExtension.Centered
import YM.Spec.Closed
import PDTAdapters.Conformal

/-!
# The same identity with the moments read in a second table, and per phase

The release's `D_cons`, `current` and `divergence` read a table `S` through its own labels
(`S.useAt S`). Its ingredients (`Table.class_smooth`, `DiffPlan.Derivatives`, `Table.classMoment`)
are stated for moments in any table `T` read through the labels of `S` (`S.useAt T`). This file
states `D_cons` and the conformal divergence identity at that generality and instantiates them at
each phase `C.ensemble i` of a selection certificate.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01 YM.TraceExtension
open scoped BigOperators ContDiff

variable {G : Gauge} {L : Register G} {S : Table L} {n d : ℕ}

/-- The release's `current`, with the moments read in a second table `T`. -/
def currentIn (T : Table L) (J : S.Stress) (V : E4 → E4) (x : Points n) (q : Fin n → S.Tag)
    (a : Axis) (y : E4) : ℂ :=
  ∑ b : Axis, V y b • S.useAt T (Points.cons y x) (Fin.cons ⟨4,J a b⟩ q)

/-- At `T = S` this is the release's `current`. -/
theorem currentIn_self (J : S.Stress) (V : E4 → E4) (x : Points n) (q : Fin n → S.Tag) :
    currentIn S J V x q = current J V x q := rfl

/-- Levels of the tag list with a level `d` in front. -/
abbrev frontCaps (d : ℕ) (q : Fin n → S.Tag) : Caps (n+1) :=
  Fin.cons (α := fun _ => ℕ) d (fun j => (q j).1)

/-- First-slot readout in a second table, as a linear map of the first label. -/
def frontIn (T : Table L) (q : Fin n → S.Tag) (x : Points (n+1)) (d : ℕ) : S.Field d →ₗ[ℂ] ℂ :=
  (S.classMoment T (frontCaps d q) x).toLinearMap
    (Fin.cons (α := fun i => S.Field (frontCaps d q i)) (0 : S.Field d) (fun j => (q j).2)) 0

theorem frontIn_eval (T : Table L) (q : Fin n → S.Tag) (x : Points (n+1)) (d : ℕ)
    (p : S.Field d) : frontIn T q x d p = S.useAt T x (Fin.cons ⟨d,p⟩ q) := by
  have hw : (Fin.cons (α := fun _ : Fin (n+1) => S.Tag) ⟨d,p⟩ q) = fun i =>
      ⟨frontCaps d q i,
        Fin.cons (α := fun i => S.Field (frontCaps d q i)) p (fun j => (q j).2) i⟩ := by
    funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  rw [hw]
  exact congrArg (S.classMoment T (frontCaps d q) x)
    (Fin.update_cons_zero (α := fun i => S.Field (frontCaps d q i)) (0 : S.Field d)
      (fun j => (q j).2) p)

theorem smooth_consIn (T : Table L) (h : T.Smooth) (v : S.Tag) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ContDiffAt ℝ ∞ (fun z => S.useAt T (Points.cons z x) (Fin.cons v q)) y := by
  have hu : ContDiff ℝ ∞ (fun p => Points.cons p x) := by
    rw [shifting_head]; exact (headDir n).contDiff.add contDiff_const
  exact (((S.class_smooth T h _ _ hy).contDiffAt ((conf_open _).mem_nhds hy))).comp y hu.contDiffAt

/-- The release's `D_cons` with the moments read in a second table `T`. -/
theorem D_consIn (T : Table L) (h : T.Smooth) (W : DiffPlan S) (hd : W.Derivatives T)
    (v : S.Field d) {x : Points n} (q : Fin n → S.Tag) {y : E4}
    (hy : Points.cons y x ∈ conf _) (a : Axis) :
    D (basis a) (fun p => S.useAt T (Points.cons p x) (Fin.cons ⟨d,v⟩ q)) y =
      S.useAt T (Points.cons y x) (Fin.cons ⟨d+1,W.deriv d a v⟩ q) := by
  let F := fun p : Points (n+1) => S.useAt T p (Fin.cons ⟨d,v⟩ q)
  let u := fun p => Points.cons p x
  have hu : HasFDerivAt u (headDir n) y := by
    unfold u; rw [shifting_head]
    exact (headDir n).hasFDerivAt.add_const _
  have he : DifferentiableAt ℝ F (u y) :=
    ((S.class_smooth T h _ _ hy).contDiffAt ((conf_open _).mem_nhds hy)).differentiableAt (by simp)
  rw [hd.kernels d a v hy]
  change fderiv ℝ (F ∘ u) y (basis a) = _
  rw [fderiv_comp y he hu.differentiableAt, hu.fderiv, ContinuousLinearMap.comp_apply,
    show headDir n (basis a) = Points.direction 0 a from ?_]
  · rfl
  · ext1 i; change Points.cons (basis a) 0 i = _
    refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, Points.direction]

/-- **The identity at a general table.** `S` supplies the labels, the plan `W` and the conserved
stress `J`; the moments are those of `T`, assumed smooth with `W` realizing its derivatives.
No `T.respects S` hypothesis is needed for the identity, but without it `S.useAt T` reads `T` on
chosen representatives of the labels of `S` (see the release's remark at `YM/Euclid/Lift.lean`);
in the per-phase theorems below it holds. -/
theorem conformal_divergenceIn (T : Table L) (hs : T.Smooth) (W : DiffPlan S)
    (hd : W.Derivatives T) {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn T J V x q a) y =
      ((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y) •
        S.useAt T (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) := by
  let F (a b : Axis) (p : E4) := S.useAt T (Points.cons p x) (Fin.cons ⟨4,J a b⟩ q)
  let Tt a b := D (basis a) (fun z => V z b) y • F a b y
  let R (a b : Axis) := V y b • S.useAt T (Points.cons y x)
    (Fin.cons ⟨4+1,W.deriv 4 a (J a b)⟩ q)
  have hf (a b : Axis) : DifferentiableAt ℝ (F a b) y :=
    (smooth_consIn T hs _ q hy).differentiableAt (by simp)
  have hp (b : Axis) : DifferentiableAt ℝ (fun z => V z b) y := (hv b).differentiable (by simp) y
  have he (a b : Axis) : D (basis a) (fun z => V z b • F a b z) y = Tt a b + R a b := by
    calc
      _ = D (basis a) (fun z => V z b) y • F a b y + V y b • D (basis a) (F a b) y := by
        unfold D; rw [fderiv_fun_smul (hp b) (hf a b)]; simp [add_comm]
      _ = _ := by
        change _ + V y b • D (basis a) (fun z => F a b z) y = _
        unfold F
        rw [D_consIn T hs W hd _ q hy a]
  have hi (a : Axis) : D (basis a) (currentIn T J V x q a) y = ∑ b : Axis, (Tt a b + R a b) := by
    change fderiv ℝ (fun z => ∑ b : Axis, V z b • F a b z) y _ = _
    rw [fderiv_fun_sum fun b _ => (show DifferentiableAt ℝ (fun z => V z b • F a b z) y from
        (hp b).smul (hf a b)), _root_.sum_apply]
    exact Finset.sum_congr rfl fun b _ => he a b
  simp_rw [hi, Finset.sum_add_distrib]
  have ht : ∑ a, ∑ b, R a b = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero
    intro b _
    simp_rw [R, ← frontIn_eval, ← Finset.smul_sum, ← map_sum, hJ.divergence, map_zero, smul_zero]
  have htr : S.useAt T (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) =
      ∑ a : Axis, F a a y := by
    simp_rw [F, ← frontIn_eval, stressTrace, map_sum]
  rw [ht, add_zero, htr]
  exact contraction (c := fun a b => D (basis a) (fun z => V z b) y) (F := fun a b => F a b y)
    (fun a b => by unfold F; rw [hJ.symmetric a b]) (fun a b => hc a b y)

/-- The Killing case at a general table: the release's `divergence` with moments in `T`. -/
theorem killing_divergenceIn (T : Table L) (hs : T.Smooth) (W : DiffPlan S)
    (hd : W.Derivatives T) {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hk : killing V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn T J V x q a) y = 0 := by
  rw [conformal_divergenceIn T hs W hd J hJ V hv (killing_conformal hk) q hy,
    killing_divergence hk, mul_zero, zero_smul]

/-- The dilation case at a general table. -/
theorem dilation_divergence_traceIn (T : Table L) (hs : T.Smooth) (W : DiffPlan S)
    (hd : W.Derivatives T) {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J)
    {x : Points n} (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn T J (fun z : E4 => z) x q a) y =
      S.useAt T (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) := by
  rw [conformal_divergenceIn T hs W hd J hJ (fun z : E4 => z)
    (fun b => (EuclideanSpace.proj b : E4 →L[ℝ] ℝ).contDiff) dilation_conformal q hy,
    dilation_divergence y]
  norm_num

section Phase
open YM.Spec

variable {C : Family G} {Z : Table C.book} {X : Algebra Z} {Y : OS.Selection Z}
  {h : Z.RealSpin}

/-- **Per phase.** In every phase `Y.ensemble i` of a materialized selection, the divergence of
the conformal current of the stress `X.energy` is the trace insertion in that phase. -/
theorem phase_conformal_divergence (M : Materializes X Y h) (i : Y.space.X) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V) {x : Points n}
    (q : Fin n → Z.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn (Y.ensemble i) X.energy V x q a) y =
      ((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y) •
        Z.useAt (Y.ensemble i) (Points.cons y x) (Fin.cons ⟨4, stressTrace X.energy⟩ q) :=
  conformal_divergenceIn (Y.ensemble i) (M.phase.states i).smooth X.derivatives
    (M.phase.calculus i) X.energy M.transport.conserved V hv hc q hy

/-- **Per phase, dilation.** -/
theorem phase_dilation_divergence_trace (M : Materializes X Y h) (i : Y.space.X)
    {x : Points n} (q : Fin n → Z.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn (Y.ensemble i) X.energy (fun z : E4 => z) x q a) y =
      Z.useAt (Y.ensemble i) (Points.cons y x) (Fin.cons ⟨4, stressTrace X.energy⟩ q) :=
  dilation_divergence_traceIn (Y.ensemble i) (M.phase.states i).smooth X.derivatives
    (M.phase.calculus i) X.energy M.transport.conserved q hy

/-- The same on the release's `Final` data: every phase of the final selection. -/
theorem final_phase_conformal_divergence {f : Extraction.Order} (F : Final C f Z) (i : F.α.space.X)
    (V : E4 → E4) (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V)
    {x : Points n} (q : Fin n → Z.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (currentIn (F.α.ensemble i) F.sector.energy V x q a) y =
      ((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y) •
        Z.useAt (F.α.ensemble i) (Points.cons y x)
          (Fin.cons ⟨4, stressTrace F.sector.energy⟩ q) :=
  phase_conformal_divergence F.phase i V hv hc q hy

end Phase
end PDTAdapters
