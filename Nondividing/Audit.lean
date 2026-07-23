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
-- The `e ≤ r` package form invokes the John placement, so it reaches E2 too.
#print axioms Nondividing.progression_comparison_le_package
#print axioms Nondividing.nonempty_package

-- Further Phase C/D/H results: gap_contained and the Phase H pigeonhole chain are
-- either parameterized over external data or purely elementary, so they reach
-- only Lean core axioms.
#print axioms Nondividing.gap_contained
#print axioms Nondividing.exists_shell_reduction
#print axioms Nondividing.shellNonDividing_dOne
#print axioms Nondividing.main_log_limit_of_upper

-- Convex-lattice John placement: reaches exactly the E2 interface `discrete_john`
-- plus Lean core axioms.
#print axioms Nondividing.coordinate_section_john
#print axioms Nondividing.section_in_gap

-- lattice_section_box is proved entirely from mathlib (projection existence via
-- dual separation), so reaches only Lean core axioms.
#print axioms Nondividing.lattice_section_box
#print axioms Nondividing.index_cardinality_bound
#print axioms Nondividing.realRank_eq_of_index
#print axioms Nondividing.integerRealSpan_eq_top
#print axioms Nondividing.smul_projNorm_mem_realBox
#print axioms Nondividing.projective_span_package
#print axioms Nondividing.duality_representation_from_projective
#print axioms Nondividing.exists_capped_combination
#print axioms Nondividing.projective_duality
#print axioms Nondividing.mem_affineSpan_projNorm_iff
#print axioms Nondividing.intrinsicInterior_convexHull_projNorm_nonempty
#print axioms Nondividing.numerology

-- Phase E projective-convexity endgame + Phase H capstone: both parameterized
-- over the deep inputs (tube inclusion / projective theorem), so core axioms only.
#print axioms Nondividing.shellNonDividing_no_positive_multiple
#print axioms Nondividing.exists_positive_nsmul_mem
#print axioms Nondividing.projective_convexity_of_tube
#print axioms Nondividing.realEval_injective
#print axioms Nondividing.main_upper_eps_of_projective

-- One-sided filling core: the ψ-transferred rounding reaches exactly the E3
-- interface `zonotope_rounding` plus Lean core axioms.
#print axioms Nondividing.zonotope_rounding_carrier
#print axioms Nondividing.evalHom_injective
#print axioms Nondividing.filling_assembly
#print axioms Nondividing.GAP.add_mem_dilatedCarrier
