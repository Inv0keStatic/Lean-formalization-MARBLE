import PEG.Counterexamples
import PEG.FiniteRawGraph

/-- info: 'PEG.Ford.cycle_not_wf' does not depend on any axioms -/
#guard_msgs in
#print axioms PEG.Ford.cycle_not_wf
/-- info: 'PEG.Raw.Nu.agrees' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Raw.Nu.agrees
/-- info: 'PEG.Counterexamples.counterexample1' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.counterexample1
/-- info: 'PEG.Counterexamples.counterexample2_end' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.counterexample2_end
/-- info: 'PEG.Counterexamples.counterexample2_follow' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.counterexample2_follow
/-- info: 'PEG.Counterexamples.counterexample3' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.counterexample3
/-- info: 'PEG.Counterexamples.counterexample4' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PEG.Counterexamples.counterexample4
/-- info: 'PEG.Counterexamples.conjecture1_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture1_false
/-- info: 'PEG.Counterexamples.conjecture2_end_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture2_end_false
/-- info: 'PEG.Counterexamples.conjecture2_follow_false' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture2_follow_false
/-- info: 'PEG.Counterexamples.conjecture2_end_any_solution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture2_end_any_solution
/-- info: 'PEG.Counterexamples.conjecture2_follow_any_solution' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture2_follow_any_solution
/-- info: 'PEG.Counterexamples.conjecture4_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms PEG.Counterexamples.conjecture4_false
/-- info: 'PEG.Counterexamples.FiniteGraph.equations_match' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.FiniteGraph.equations_match
/-- info: 'PEG.Counterexamples.FiniteGraph.counterexample1_finite' depends on axioms: [propext] -/
#guard_msgs in
#print axioms PEG.Counterexamples.FiniteGraph.counterexample1_finite

#check PEG.Counterexamples.FiniteGraph.counterexample1_finite
#check PEG.Counterexamples.counterexample2_end
#check PEG.Counterexamples.counterexample2_follow
#check PEG.Counterexamples.counterexample3
#check PEG.Counterexamples.counterexample4
