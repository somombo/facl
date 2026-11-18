import Facl.Spec
import Facl.Theorems
import Facl.Examples
import Facl.Lift
import Facl.Refinement
import Lean.Util.CollectAxioms

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``Facl.combine_eq_allow_iff, ``Facl.match_length_of_not_rest,
      ``Facl.match_instantiate, ``Facl.decide_eq_allow_iff, ``Facl.default_deny,
      ``Facl.decide_perm, ``Facl.decide_mono,
      ``FaclCore.decide.combine_spec, ``FaclCore.decide.combine_allow_iff] do
    let unexpected := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
