import YM.Work.A01.Conserve
import YM.TraceExtension.Centered
import PDTAdapters.Conformal

/-!
# The divergence of a conformal current is `(∂·V)/4` times the trace insertion

For the release's conserved stress `J` on a smooth table `S` read through its own labels, and a
conformal Killing field `V`, the divergence of the release's `current J V` at separated points is
a quarter of the divergence of `V` times the correlator with the trace label `stressTrace J`
inserted. The release's `divergence` (Killing fields) is the zero-divergence case.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YM YM.Table YM.Analysis YM.Work.A01 YM.TraceExtension
open scoped BigOperators ContDiff

variable {G : Gauge} {L : Register G} {S : Table L} {n : ℕ}

/-- The trace label inserted in the first slot is the sum of the diagonal insertions. -/
theorem front_trace (J : S.Stress) (q : Fin n → S.Tag) (x : Points (n+1)) :
    S.useAt S x (Fin.cons ⟨4, stressTrace J⟩ q) =
      ∑ a : Axis, S.useAt S x (Fin.cons ⟨4, J a a⟩ q) := by
  simp_rw [← front_eval, stressTrace, map_sum]

/-- The zero label inserted in the first slot reads zero. -/
theorem front_zero (q : Fin n → S.Tag) (x : Points (n+1)) (d : ℕ) :
    S.useAt S x (Fin.cons ⟨d, (0 : S.Field d)⟩ q) = 0 := by
  rw [← front_eval, map_zero]

/-- **The identity.** Hypotheses of the release's `YM.Work.A01.divergence`, with `conformal V`
in place of `killing V`. The scalar action is the real action on `ℂ`, as in `current`.
The proof follows the release's proof of `YM.Work.A01.divergence` (`YM/Work/A01/Conserve.lean`)
up to its last step, where `contraction` takes the place of the antisymmetry argument. -/
theorem conformal_divergence (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S)
    {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current J V x q a) y =
      ((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y) •
        S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) := by
  let F (a b : Axis) (p : E4) := S.useAt S (Points.cons p x) (Fin.cons ⟨4,J a b⟩ q)
  let T a b := D (basis a) (fun z => V z b) y • F a b y
  let R (a b : Axis) := V y b • S.useAt S (Points.cons y x)
    (Fin.cons ⟨4+1,W.deriv 4 a (J a b)⟩ q)
  have hf (a b : Axis) : DifferentiableAt ℝ (F a b) y :=
    (smooth_cons S hs _ q hy).differentiableAt (by simp)
  have hp (b : Axis) : DifferentiableAt ℝ (fun z => V z b) y := (hv b).differentiable (by simp) y
  have he (a b : Axis) : D (basis a) (fun z => V z b • F a b z) y = T a b + R a b := by
    calc
      _ = D (basis a) (fun z => V z b) y • F a b y + V y b • D (basis a) (F a b) y := by
        unfold D; rw [fderiv_fun_smul (hp b) (hf a b)]; simp [add_comm]
      _ = _ := by
        change _ + V y b • D (basis a) (fun z => F a b z) y = _
        unfold F
        rw [D_cons hs W hd _ q hy a]
  have hi (a : Axis) : D (basis a) (current J V x q a) y = ∑ b : Axis, (T a b + R a b) := by
    change fderiv ℝ (fun z => ∑ b : Axis, V z b • F a b z) y _ = _
    rw [fderiv_fun_sum fun b _ => (show DifferentiableAt ℝ (fun z => V z b • F a b z) y from
        (hp b).smul (hf a b)), _root_.sum_apply]
    exact Finset.sum_congr rfl fun b _ => he a b
  simp_rw [hi, Finset.sum_add_distrib]
  have ht : ∑ a, ∑ b, R a b = 0 := by
    rw [Finset.sum_comm]; apply Finset.sum_eq_zero
    intro b _
    simp_rw [R, ← front_eval, ← Finset.smul_sum, ← map_sum, hJ.divergence, map_zero, smul_zero]
  rw [ht, add_zero, front_trace]
  exact contraction (c := fun a b => D (basis a) (fun z => V z b) y) (F := fun a b => F a b y)
    (fun a b => by unfold F; rw [hJ.symmetric a b]) (fun a b => hc a b y)

/-- The same identity with the real factor coerced to `ℂ` and the complex action. -/
theorem conformal_divergence_ofReal (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S)
    {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hc : conformal V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current J V x q a) y =
      (((1/4 : ℝ) * ∑ c : Axis, D (basis c) (fun z => V z c) y : ℝ) : ℂ) •
        S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) := by
  rw [conformal_divergence hs W hd J hJ V hv hc q hy, Complex.real_smul, smul_eq_mul]

/-- The statement of the release's `YM.Work.A01.divergence`, derived from `conformal_divergence`
and `killing_conformal`: the case of zero divergence. -/
theorem divergence_of_conformal_killing (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S)
    {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) (V : E4 → E4)
    (hv : ∀ b : Axis, ContDiff ℝ ∞ (fun z => V z b)) (hk : killing V) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current J V x q a) y = 0 := by
  rw [conformal_divergence hs W hd J hJ V hv (killing_conformal hk) q hy, killing_divergence hk,
    mul_zero, zero_smul]

/-- The corollary has literally the statement of the release's theorem. -/
example : @divergence_of_conformal_killing = @YM.Work.A01.divergence := rfl

/-- Smoothness of the coordinates of the dilation field. -/
theorem dilation_smooth (b : Axis) : ContDiff ℝ ∞ (fun z : E4 => (fun y : E4 => y) z b) :=
  (EuclideanSpace.proj b : E4 →L[ℝ] ℝ).contDiff

/-- **The dilation case.** The divergence of the dilation current is the trace insertion. -/
theorem dilation_divergence_trace (hs : S.Smooth) (W : DiffPlan S) (hd : W.Derivatives S)
    {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) {x : Points n}
    (q : Fin n → S.Tag) {y : E4} (hy : Points.cons y x ∈ conf _) :
    ∑ a : Axis, D (basis a) (current J (fun z : E4 => z) x q a) y =
      S.useAt S (Points.cons y x) (Fin.cons ⟨4, stressTrace J⟩ q) := by
  rw [conformal_divergence hs W hd J hJ (fun z : E4 => z) dilation_smooth dilation_conformal q hy,
    dilation_divergence y]
  norm_num

/-- Every configuration of `n+1` points is its first point put in front of the rest. -/
theorem cons_head_tail (x : Points (n+1)) : Points.cons (x 0) (Points.tail x) = x := by
  apply PiLp.ext; intro i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [Points.cons, Points.tail]

/-- **The characterization.** For a conserved stress on a symmetric smooth table, the trace
label vanishes exactly when the dilation current is divergence-free at every separated
configuration, with every list of spectator tags. Here `stressTrace J = 0` is equality in the
quotient `S.Field 4`, i.e. the trace is null in the own table's separated correlators; the statement
is for the own table only, and `hp` is used only in the reverse direction (through `field_ext`). -/
theorem stressTrace_eq_zero_iff (hp : S.Symmetric) (hs : S.Smooth) (W : DiffPlan S)
    (hd : W.Derivatives S) {H : S.RealSpin} (J : S.Stress) (hJ : Conserved W H J) :
    stressTrace J = 0 ↔
      ∀ (n : ℕ) (x : Points n) (q : Fin n → S.Tag) (y : E4), Points.cons y x ∈ conf (n+1) →
        ∑ a : Axis, D (basis a) (current J (fun z : E4 => z) x q a) y = 0 := by
  constructor
  · intro h0 n x q y hy
    rw [dilation_divergence_trace hs W hd J hJ q hy, h0, front_zero]
  · intro h
    apply S.field_ext hp
    intro n q x hx
    have hx' : Points.cons (x 0) (Points.tail x) ∈ conf (n+1) := by
      rw [cons_head_tail]; exact hx
    have key := h n (Points.tail x) q (x 0) hx'
    rw [dilation_divergence_trace hs W hd J hJ q hx', cons_head_tail] at key
    rw [key, front_zero]

end PDTAdapters
