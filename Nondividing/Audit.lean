import Nondividing.Main

#print axioms Nondividing.lower_construction
#print axioms Nondividing.main_lower_eps

-- Phase C progression-comparison assemblies (parameterized over E1 outputs):
-- these must reach only Lean core axioms, since E1–E5 enter only through their
-- hypotheses, not through any axiom in the proof term.
#print axioms Nondividing.GAP.progression_comparison_gt
#print axioms Nondividing.GAP.progression_comparison_le

-- Package-based progression comparison is parameterized over an abstract
-- `Package`, so it reaches only Lean core axioms; the E1 interface
-- `cfp_structure` enters exactly where the concrete package is built.
#print axioms Nondividing.progression_comparison_package
#print axioms Nondividing.nonempty_package
