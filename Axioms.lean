import PDTAdapters
import PDTAdapters.FreeControl

/-!
# Axioms of every declaration of the six modules

Not part of the library. Copy this file into the checkout of the release beside
`PDTAdapters.lean`, build `PDTAdapters` and `PDTAdapters.FreeControl`, and run

    lake env lean -DmaxHeartbeats=0 -DmaxRecDepth=4096 Axioms.lean

The expected output is 47 lines, each ending in `[propext, Classical.choice, Quot.sound]`
(recorded in `BUILD.txt`).
-/

-- Conformal.lean
#print axioms PDTAdapters.conformal
#print axioms PDTAdapters.killing_diagonal
#print axioms PDTAdapters.killing_divergence
#print axioms PDTAdapters.killing_conformal
#print axioms PDTAdapters.D_coordinate
#print axioms PDTAdapters.dilation_divergence
#print axioms PDTAdapters.dilation_conformal
#print axioms PDTAdapters.contraction
-- Divergence.lean
#print axioms PDTAdapters.front_trace
#print axioms PDTAdapters.front_zero
#print axioms PDTAdapters.conformal_divergence
#print axioms PDTAdapters.conformal_divergence_ofReal
#print axioms PDTAdapters.divergence_of_conformal_killing
#print axioms PDTAdapters.dilation_smooth
#print axioms PDTAdapters.dilation_divergence_trace
#print axioms PDTAdapters.cons_head_tail
#print axioms PDTAdapters.stressTrace_eq_zero_iff
-- General.lean
#print axioms PDTAdapters.currentIn
#print axioms PDTAdapters.currentIn_self
#print axioms PDTAdapters.frontCaps
#print axioms PDTAdapters.frontIn
#print axioms PDTAdapters.frontIn_eval
#print axioms PDTAdapters.smooth_consIn
#print axioms PDTAdapters.D_consIn
#print axioms PDTAdapters.conformal_divergenceIn
#print axioms PDTAdapters.killing_divergenceIn
#print axioms PDTAdapters.dilation_divergence_traceIn
#print axioms PDTAdapters.phase_conformal_divergence
#print axioms PDTAdapters.phase_dilation_divergence_trace
#print axioms PDTAdapters.final_phase_conformal_divergence
-- Det.lean
#print axioms PDTAdapters.det_invariant
-- TraceStep.lean
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
-- FreeControl.lean
#print axioms PDTAdapters.polStress_trace
#print axioms PDTAdapters.free_stressTrace
#print axioms PDTAdapters.free_dilation_divergence
