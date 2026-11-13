import PDTAdapters.Conformal
import PDTAdapters.Divergence
import PDTAdapters.General
import PDTAdapters.Det
import PDTAdapters.TraceStep

/-!
# PDTAdapters

Theorems stated on the definitions of the Yang–Mills release (`YM.*`), added beside it without
modifying it.

Scope. These are separated-point identities: pointwise derivative identities for correlators at
configurations in `conf` (all points distinct). They extend the release's `YM.Work.A01.divergence`
from Killing fields to conformal Killing fields. They are NOT the contact or dilation Ward identities
(which carry coincident-point terms and a dilation action on the inserted fields), and they do not
bear on improvement uniqueness: they hold for every `J` satisfying `Conserved`.
The theorems of `PDTAdapters.TraceStep` are stated at separated pairs, and at the configurations
`opposed r` on a `Spec.Final`; `selected_dilation_rate` and `selected_dilation_not_conserved` are
implications from a hypothesis on `euclidean F` that this library does not prove.

* `PDTAdapters.conformal`, `killing_conformal`, `dilation_conformal`, `dilation_divergence`
* `PDTAdapters.conformal_divergence` — the divergence of a conformal current is the trace insertion
* `PDTAdapters.divergence_of_conformal_killing` — the release's `divergence` as a corollary
* `PDTAdapters.dilation_divergence_trace`, `PDTAdapters.stressTrace_eq_zero_iff`
* `PDTAdapters.conformal_divergenceIn`, `PDTAdapters.phase_conformal_divergence` — general table, per phase
* `PDTAdapters.det_invariant` — invariant symmetric endomorphisms of the colour space
* `PDTAdapters.dilation_divergence_centerIn`, `PDTAdapters.selected_dilation_divergence`,
  `PDTAdapters.selected_dilation_divergence_at`, `PDTAdapters.selected_dilation_rate`,
  `PDTAdapters.selected_dilation_not_conserved` — the divergence of the dilation current against a
  centred spectator; the last two in hypothesis form
-/

#print axioms PDTAdapters.killing_conformal
#print axioms PDTAdapters.dilation_conformal
#print axioms PDTAdapters.dilation_divergence
#print axioms PDTAdapters.conformal_divergence
#print axioms PDTAdapters.conformal_divergence_ofReal
#print axioms PDTAdapters.divergence_of_conformal_killing
#print axioms PDTAdapters.dilation_divergence_trace
#print axioms PDTAdapters.stressTrace_eq_zero_iff
#print axioms PDTAdapters.D_consIn
#print axioms PDTAdapters.conformal_divergenceIn
#print axioms PDTAdapters.phase_conformal_divergence
#print axioms PDTAdapters.phase_dilation_divergence_trace
#print axioms PDTAdapters.final_phase_conformal_divergence
#print axioms PDTAdapters.det_invariant
#print axioms PDTAdapters.at_unitIn
#print axioms PDTAdapters.centered_front
#print axioms PDTAdapters.dilation_divergence_centerIn
#print axioms PDTAdapters.rate_ne_zero
#print axioms PDTAdapters.rate_zero_control
#print axioms PDTAdapters.opposed_conf
#print axioms PDTAdapters.opposed_conf_of_ne
#print axioms PDTAdapters.selected_dilation_divergence_of_ne
#print axioms PDTAdapters.selected_dilation_divergence
#print axioms PDTAdapters.selected_axis_shape
#print axioms PDTAdapters.selected_dilation_divergence_at
#print axioms PDTAdapters.selected_dilation_rate
#print axioms PDTAdapters.selected_dilation_not_conserved
