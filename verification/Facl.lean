import Facl.Spec
import Facl.Cel
import Facl.Theorems
import Facl.Examples
import Facl.Lift
import Facl.Refinement
import Facl.RefinementPath
import Facl.RefinementDecide
import Facl.RefinementRequest
import Facl.PathTheorems
import Facl.RefinementLower
import Facl.RefinementEvaluate
import Lean.Util.CollectAxioms

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``Facl.combine_eq_allow_iff, ``Facl.match_length_of_not_rest,
      ``Facl.match_instantiate, ``Facl.decide_eq_allow_iff, ``Facl.default_deny,
      ``Facl.decide_perm, ``Facl.decide_mono,
      ``Facl.utf8Valid_iff, ``Facl.canonicalize_segment, ``Facl.lower_allow_methods,
      ``FaclCore.decide.combine_spec, ``FaclCore.decide.combine_allow_iff,
      ``FaclCore.decide.decide_with_spec, ``FaclCore.path.match_pattern_spec,
      ``FaclCore.decide.method_bit_spec, ``FaclCore.path.canonicalize_spec,
      ``FaclCore.decide.action_bits_spec, ``FaclCore.lower.lower_with_spec,
      ``FaclCore.decide.evaluate_with_spec] do
    let unexpected := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
