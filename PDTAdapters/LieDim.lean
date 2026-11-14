import PDTAdapters.OnConstructed

/-!
# The release's constant `Trace.Verse.award` and the dimension of the Lie algebra

The release defines `YM.Trace.Verse.award G := 12 * (d2 G ^ 2 / b0 G ^ 2) * G.lieDim / π ^ 4`
(`YM/TraceExtension/Verse/Day.lean`, line 41), with `d2 G = -b0 G / 2` (`force_b`) and
`b0 G = 11 * G.casimir / (48 * π ^ 2)` (both in `YM/TraceExtension/Chart/Nectar.lean`). Here
`G.lieDim` is `Module.finrank ℝ G.Alg`, the dimension of the gauge Lie algebra
(`YM/Gauge/Colors.lean`). If `G.casimir ≠ 0`, then `b0 G ≠ 0`, the ratio `d2 G ^ 2 / b0 G ^ 2` is
`1/4`, and `award G = 3 * G.lieDim / π ^ 4`; for a simple `G` the Casimir is positive
(`YM.Gauge.casimir_pos`).

The release has this value already. It proves it for `g.core` of a simple
`YangMills.GaugeGroup` as the private theorem `award_eq` (`TraceBridge.lean`, lines 24–33), and
inline in a proof (`YM/TraceExtension/Link/Rad.lean`, lines 98–100). Its public specification
states the same value as the limit of `r⁸ (log r⁻¹)²` times the trace two-point function
`traceTwo` (`ChallengeSpec.lean`, lines 172–174, the structure `Hierarchy.TraceTest`), which the
release's `publicTrace` (`TraceBridge.lean`, line 35) proves from `TraceExclusions`. This file
states the value as a public theorem for every `YM.Gauge` with nonzero Casimir, and carries it to
the rate of the divergence of the dilation current (`headline_dilation_rate`).

* `award_eq_three_mul_lieDim_of_casimir_ne_zero` — if `G.casimir ≠ 0`,
  `Trace.Verse.award G = 3 * G.lieDim / π ^ 4`.
* `award_eq_three_mul_lieDim` — the same for a simple `G`, from the previous theorem by
  `YM.Gauge.casimir_pos`.
* `award_eq_zero_of_casimir_eq_zero` — a control: if `G.casimir = 0`, then `Trace.Verse.award G`
  is `0`.
* `headline_dilation_rate_lieDim` — `headline_dilation_rate` (`PDTAdapters/OnHeadline.lean`) with
  the limit written `3 * G.lieDim / π ^ 4`, under `H : Headline.TraceExclusions F` alone
  (`H.positive` gives `award G ≠ 0`, hence `G.casimir ≠ 0`).
* `constructed_dilation_rate_lieDim` — for the release's construction (`YangMills.constructed`,
  through `constructed_dilation` of `PDTAdapters/OnConstructed.lean`): for every simple `g` and
  every `b > 0`, the family `C` with penalty `b` and `C.Makes`, and for every order `p` a table
  `S` and an `F` with `Headline.TraceExclusions F` and the rate, with the limit written
  `3 * g.core.lieDim / π ^ 4`.
* `su2_lieDim` — the Lie algebra of the release's `YangMills.su2` has dimension `3`.
* `su2_dilation_rate` — `constructed_dilation_rate_lieDim` at the release's `YangMills.su2`,
  `YangMills.su2Simple` and `b = 1`, with the limit `9 / π ^ 4`.

The `example` after `constructed_dilation_rate_lieDim` checks in the kernel that the statement of
`headline_dilation_rate_lieDim` is that of `headline_dilation_rate` with
`Trace.Verse.award G` rewritten by `award_eq_three_mul_lieDim_of_casimir_ne_zero`.

For `su2_lieDim` the file copies private lemmas of the release's `YM/Examples/SU2.lean` (see the
section before it).

Checked against the restored public compiled build of the release, not compiled from the
release's source on this machine; no kernel replay of the release's declarations. All
configurations are in `conf` (distinct points). Nothing here concerns coincident points.
-/

set_option autoImplicit false
noncomputable section
namespace PDTAdapters
open YangMills YM YM.Spec YM.OPE.Orbits YM.Nonperturbative
open YM.Table YM.Analysis YM.TraceExtension Filter
open scoped BigOperators Topology

universe u v

section Award

variable {G : YM.Gauge}

/-- **The constant, written out.** If the Casimir of `G` is not zero, the release's constant
`Trace.Verse.award G` is three times the dimension `G.lieDim` of the gauge Lie algebra, over
`π⁴`. The proof unfolds `award`, rewrites `d2 G` by the release's `force_b`, and uses
`G.casimir ≠ 0` for `b0 G ≠ 0`. It follows the release's step at
`YM/TraceExtension/Link/Rad.lean`, lines 98–100. -/
theorem award_eq_three_mul_lieDim_of_casimir_ne_zero (h : G.casimir ≠ 0) :
    Trace.Verse.award G = 3 * (G.lieDim : ℝ) / Real.pi ^ 4 := by
  have hn : YM.Trace.Over.b0 G ≠ 0 := by
    unfold YM.Trace.Over.b0; have := Real.pi_pos; positivity
  unfold Trace.Verse.award
  rw [YM.Trace.Over.force_b]
  field_simp
  ring

/-- **The constant, for a simple gauge group.** For a simple `G` the Casimir is positive
(`YM.Gauge.casimir_pos`), so `Trace.Verse.award G = 3 * G.lieDim / π⁴` by
`award_eq_three_mul_lieDim_of_casimir_ne_zero`. -/
theorem award_eq_three_mul_lieDim (h : G.Simple) :
    Trace.Verse.award G = 3 * (G.lieDim : ℝ) / Real.pi ^ 4 :=
  award_eq_three_mul_lieDim_of_casimir_ne_zero (YM.Gauge.casimir_pos h).ne'

/-- **Control.** If `G.casimir = 0`, then `b0 G = 0` and the release's definition gives
`Trace.Verse.award G = 0` (division by zero in `ℝ` is `0`). So the value `3 * G.lieDim / π⁴`
needs `G.casimir ≠ 0`. No `G` with `G.casimir = 0` and `G.lieDim ≠ 0` is constructed here. -/
theorem award_eq_zero_of_casimir_eq_zero (h : G.casimir = 0) : Trace.Verse.award G = 0 := by
  unfold Trace.Verse.award YM.Trace.Over.b0
  simp [h]

end Award

section Headline

variable {G : YM.Gauge} {C : YM.Family G} {f : Extraction.Order} {S : Table C.book}
variable (F : YM.Spec.Final C f S)

/-- **The rate, with the constant written out.** Under `H : Headline.TraceExclusions F`, the
multiple `s⁸ (log s⁻¹)²` of the divergence of the dilation current at `opposed s` tends to
`3 * G.lieDim / π⁴` as `s → 0⁺`. No further hypothesis on `G` is needed: `H.positive` gives
`Trace.Verse.award G ≠ 0`, hence `G.casimir ≠ 0` by `award_eq_zero_of_casimir_eq_zero`. The
proof rewrites the limit by `award_eq_three_mul_lieDim_of_casimir_ne_zero` and applies
`headline_dilation_rate`. -/
theorem headline_dilation_rate_lieDim
    (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
        ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
          (YM.Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a)
          (opposed s 0))
      (𝓝[>] 0) (𝓝 ((3 * (G.lieDim : ℝ) / Real.pi ^ 4 : ℝ) : ℂ)) := by
  rw [← award_eq_three_mul_lieDim_of_casimir_ne_zero
    (fun hc => H.positive.ne' (award_eq_zero_of_casimir_eq_zero hc))]
  exact headline_dilation_rate F H

end Headline

/-- **The rate for the release's construction, with the constant written out.** For every simple
`g` and every `b > 0` there is a family `C` with penalty `b` and `C.Makes` such that, for every
order `p`, there are `q`, a table `S` and `F : Final C (p.refine q) S` with
`Headline.TraceExclusions F` and: the multiple `s⁸ (log s⁻¹)²` of the divergence of the dilation
current of `F.sector.energy` at `opposed s`, read in `selected F` against the spectator
`center F`, tends to `3 * g.core.lieDim / π⁴` as `s → 0⁺`. The proof projects
`constructed_dilation` (the witness is that of `YangMills.constructed`) and rewrites its limit by
`award_eq_three_mul_lieDim` at `GaugeGroup.coreSimple hg`. -/
theorem constructed_dilation_rate_lieDim (g : GaugeGroup) (hg : g.IsSimple) (b : ℝ)
    (hb : 0 < b) :
    ∃ C : YM.Family g.core, C.path.levels.clock.kernel.penalty = b ∧ C.Makes ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S), Headline.TraceExclusions.{u,v} F ∧
        Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
            ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
              (YM.Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a)
              (opposed s 0))
          (𝓝[>] 0) (𝓝 ((3 * (g.core.lieDim : ℝ) / Real.pi ^ 4 : ℝ) : ℂ)) := by
  obtain ⟨C, penalty, makes, -, orders⟩ := constructed_dilation.{u,v} g hg b hb
  refine ⟨C, penalty, makes, fun p => ?_⟩
  obtain ⟨q, S, F, -, -, -, -, -, -, -, -, -, -, -, -, -, -, trace, -, -, -, -, -, -, rate,
    -⟩ := orders p
  refine ⟨q, S, F, trace, ?_⟩
  rw [← award_eq_three_mul_lieDim (GaugeGroup.coreSimple hg)]
  exact rate

/-- The statement of `headline_dilation_rate_lieDim` is that of `headline_dilation_rate` with
`Trace.Verse.award G` rewritten by `award_eq_three_mul_lieDim_of_casimir_ne_zero` (an equality of
the two propositions, closed by that rewrite alone). -/
example {G : YM.Gauge} {C : YM.Family G} {f : Extraction.Order} {S : Table C.book}
    (F : YM.Spec.Final C f S)
    (H : YM.Nonperturbative.Headline.TraceExclusions.{u,v} F) :
    type_of% (headline_dilation_rate_lieDim F H) = type_of% (headline_dilation_rate F H) := by
  rw [award_eq_three_mul_lieDim_of_casimir_ne_zero
    (fun hc => H.positive.ne' (award_eq_zero_of_casimir_eq_zero hc))]

end PDTAdapters

/-! ### The dimension of the Lie algebra of the release's SU(2)

The release's `YM/Examples/SU2.lean` proves `YM.Examples.SU2.simple` with private lemmas on three
generators `A`, `B`, `C` of the Lie algebra of `YM.Next.Foundations.SUtwo` (membership, and that
every element is a real combination of them). Being private, they cannot be used from here. The
declarations of this namespace up to `express` are copies of those lemmas (statements and proofs,
with `SUtwo` written for the release's local abbreviation `G`); `gens_li` and `gens_span` show that
the three generators are linearly independent over `ℝ` and span the Lie algebra. -/

namespace PDTAdapters.SU2Lie
open Matrix Function Filter NormedSpace YM YM.Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators

private abbrev M := Matrix (Fin 2) (Fin 2) ℂ
private abbrev A : M := !![Complex.I,0;0,-Complex.I]
private abbrev B : M := !![0,1;-1,0]
private abbrev C : M := !![0,Complex.I;Complex.I,0]

private lemma lies (X:M) (hh:star X = -X)(ht:X*X= -(1:M))
    (h:∀ (c s:ℝ),s^2+c^2=1 → det (c • (1:M)+s • X)=1) : X∈ SUtwo.lie:= by
    let f(z:ℝ): M:= Real.cos z • (1:M)+ Real.sin z • X
    have hF : HasDerivAt f X 0:= by
        have hh:= ((Real.hasDerivAt_cos 0).smul_const (1:M)).add ((Real.hasDerivAt_sin 0).smul_const X); simpa using! hh
    refine SUtwo.tangent_generates (f:=f) hF (by change f 0 = (1:M); simp [f]) fun t=>?_
    let s:= Real.sin t; let c:= Real.cos t; have he:s^2+c^2=1:=Real.sin_sq_add_cos_sq t
    have hz: f t ∈ unitary M:= by
        apply Matrix.mem_unitaryGroup_iff.mpr
        change (c • (1:M)+ s • X) * star (c • (1:M)+ s • X)= _
        rw [star_add,star_smul,star_smul,star_one, hh]; simp_rw [star_trivial]; rw [mul_add,add_mul,add_mul, smul_mul_smul_comm, smul_mul_smul_comm, smul_mul_smul_comm,smul_mul_smul_comm,one_mul,one_mul,mul_one,mul_neg,ht];
        rw[neg_neg];
        conv_rhs=> rw [← one_smul ℝ (1:M),← he]
        module
    let x : GaugeU SUtwo.n := ⟨f t,hz⟩; have hx:x∈ SUtwo.imageGroup:= h c s he
    exact ⟨⟨x,hx⟩,rfl⟩

local macro "entry" : tactic => `(tactic| (ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.star_eq_conjTranspose, Complex.star_def,A,B,C,Matrix.mul_apply,Fin.sum_univ_two,Complex.mul_re,Complex.mul_im, Complex.neg_im]))
private lemma a_in : A∈ SUtwo.lie:=by
   apply lies (X:=A)
   · entry
   · entry
   intro c s he; rw [Matrix.det_fin_two]; norm_num [A,Complex.real_smul]; ring_nf; simp; exact_mod_cast ((add_comm (c^2) _).trans he : c^2+s^2=1)
private lemma b_in:B∈ SUtwo.lie:=by
   apply lies (X:=B)
   · entry
   · entry
   intro c s he; rw [Matrix.det_fin_two]; norm_num [B,Complex.real_smul];ring_nf; norm_cast; linarith only[he]
private abbrev comm(x y:M):M:=x*y-y*x
private lemma ab : comm A B=(2:ℝ) • C:=by unfold comm;rw [two_smul];entry
private lemma drank {L:Submodule ℝ M}{x:M}{c:ℝ}(h:c • x∈L)(he:c≠0):x∈L:=by simpa only[smul_smul,inv_mul_cancel₀ he,one_smul] using L.smul_mem c⁻¹ h
private lemma c_in:C∈ SUtwo.lie:=drank (c:=2) (ab ▸ (show comm A B∈SUtwo.lie from SUtwo.bracket_mem a_in b_in)) (by norm_num)

private lemma trzero(X:M)(ht:X∈ SUtwo.lie): X 0 0+X 1 1=0:=by
    let f(t:ℝ):= NormedSpace.exp (t • X)
    have hV:HasDerivAt f X 0:=by simpa only[zero_smul,NormedSpace.exp_zero,one_mul] using! hasDerivAt_exp_smul_const X (0:ℝ)
    have hv(t:ℝ):det (f t)=1:=by
        obtain ⟨q,hp⟩:= (show SUtwo.Generates X from ht) t
        change SUtwo.mat q=f t at hp; rw[← hp]; exact q.property
    have hh(i j:Fin 2):HasDerivAt (fun t=> f t i j) (X i j) 0:=by
        let A : M →L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun:=fun y=> y i j, map_add':=fun _ _ => rfl, map_smul':=fun _ _=> rfl }
        exact A.hasFDerivAt.comp_hasDerivAt _ hV
    have hz:= ((hh 0 0).mul (hh 1 1)).sub ((hh 0 1).mul (hh 1 0));
    have hH: HasDerivAt (fun t=> det (f t)) _ 0 := hz.congr_of_eventuallyEq (Eventually.of_forall (fun t=> Matrix.det_fin_two ..))
    simp_rw [hv] at hH; simpa only [show f 0=(1:M) by simp [f],Matrix.one_apply, ite_true, show ¬(1:Fin 2)=0 from by decide, show ¬(0:Fin 2)=1 from by decide, ite_false, zero_mul,mul_zero,one_mul,mul_one,sub_zero, zero_add, ↓reduceIte] using hH.unique (hasDerivAt_const ..)
private lemma express(X:M)(ht:X∈ SUtwo.lie):∃ a b c:ℝ, X=a • A+b • B+c • C:=by
    have he:= trzero X ht
    let a:=(X 0 0).im; let b:=(X 0 1).re; let c:=(X 0 1).im; refine ⟨a,b,c,?_⟩
    have hp(x y:Fin 2): (star (X y x))= -(X x y):= congr_fun (congr_fun (SUtwo.generates_skew ht) x) y
    have hX: (X 1 1)= -(X 0 0):= (neg_eq_iff_add_eq_zero.mpr he).symm
    have hY:(X 1 0)= -(star (X 0 1)):=by rw [hp,neg_neg]
    have hz: (X 0 0).re=0:=by have hu:=congr_arg Complex.re (hp 0 0); simp only [Complex.star_def,Complex.conj_re,Complex.neg_re] at hu;linarith only[hu]
    ext i j;fin_cases i<;> fin_cases j<;> simp [A,B,C,Complex.real_smul,hX,hY,a,b,c]<;> apply Complex.ext<;> simp[hz]

private def gens : Fin 3 → SUtwo.Alg := ![⟨A, a_in⟩, ⟨B, b_in⟩, ⟨C, c_in⟩]

private lemma gens_li : LinearIndependent ℝ gens := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hm := congrArg (fun x : SUtwo.Alg => x.1) hg
  simp [Fin.sum_univ_three, gens] at hm
  have h00 := congrArg Complex.im (congr_fun (congr_fun hm 0) 0)
  have h01r := congrArg Complex.re (congr_fun (congr_fun hm 0) 1)
  have h01i := congrArg Complex.im (congr_fun (congr_fun hm 0) 1)
  change (g 0 • Complex.I + g 1 • (0:ℂ) + g 2 • (0:ℂ)).im = (0:ℂ).im at h00
  change (g 0 • (0:ℂ) + g 1 • (1:ℂ) + g 2 • Complex.I).re = (0:ℂ).re at h01r
  change (g 0 • (0:ℂ) + g 1 • (1:ℂ) + g 2 • Complex.I).im = (0:ℂ).im at h01i
  simp at h00 h01r h01i
  intro i; fin_cases i <;> simpa

private lemma gens_span : ⊤ ≤ Submodule.span ℝ (Set.range gens) := by
  rintro ⟨X, hX⟩ -
  obtain ⟨a, b, c, rfl⟩ := express X hX
  have : (⟨a • A + b • B + c • C, hX⟩ : SUtwo.Alg) = a • gens 0 + b • gens 1 + c • gens 2 := by
    ext1; rfl
  rw [this]
  refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_ <;>
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)


private theorem sutwo_lieDim : SUtwo.lieDim = 3 := by
  rw [YM.Gauge.lieDim, Module.finrank_eq_card_basis (Module.Basis.mk gens_li gens_span),
    Fintype.card_fin]

end PDTAdapters.SU2Lie

namespace PDTAdapters
open YangMills YM YM.Spec YM.OPE.Orbits YM.Nonperturbative
open YM.Table YM.Analysis YM.TraceExtension Filter
open scoped BigOperators Topology

universe u v

/-- **The Lie algebra of the release's SU(2) has dimension three.** `YangMills.su2.core` is the
release's `YM.Next.Foundations.SUtwo` (the determinant-one matrices of `U(2)`), and the dimension of
its Lie algebra over `ℝ` is `3`: the three generators of the release's `YM/Examples/SU2.lean` are a
basis. -/
theorem su2_lieDim : su2.core.lieDim = 3 := SU2Lie.sutwo_lieDim

/-- **The rate at the release's SU(2).** `constructed_dilation_rate_lieDim` at `YangMills.su2`,
`YangMills.su2Simple` and `b = 1`, with `su2_lieDim`: the limit is `3 · 3 / π⁴ = 9 / π⁴`. -/
theorem su2_dilation_rate :
    ∃ C : YM.Family su2.core, C.path.levels.clock.kernel.penalty = 1 ∧ C.Makes ∧
      ∀ p : Extraction.Order, ∃ (q : Extraction.Order) (S : Table C.book)
        (F : Final C (p.refine q) S), Headline.TraceExclusions.{u,v} F ∧
        Tendsto (fun s : ℝ => ((s^8 * (Real.log s⁻¹)^2) : ℝ) •
            ∑ a : YM.Axis, D (basis a) (currentIn (selected F) F.sector.energy (fun z : E4 => z)
              (YM.Points.tail (opposed s)) (fun _ : Fin 1 => (⟨4, center F⟩ : S.Tag)) a)
              (opposed s 0))
          (𝓝[>] 0) (𝓝 ((9 / Real.pi ^ 4 : ℝ) : ℂ)) := by
  have e : 3 * ((su2.core.lieDim : ℕ) : ℝ) / Real.pi ^ 4 = 9 / Real.pi ^ 4 := by
    rw [su2_lieDim]; norm_num
  have h := constructed_dilation_rate_lieDim.{u,v} su2 su2Simple 1 one_pos
  rw [e] at h
  exact h

end PDTAdapters
