import Facl.Spec
import Facl.Theorems
import Facl.Examples
import Facl.Refinement
import Lean.Util.CollectAxioms

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  for decl in [``FaclCore.decide.combine_spec, ``FaclCore.decide.combine_allow_iff] do
    let unexpected := (← Lean.collectAxioms decl).filter fun ax => !allowed.contains ax
    unless unexpected.isEmpty do
      throwError "{decl} depends on unexpected axioms {unexpected}"
