import Facl.Spec
import FaclCore.Types

namespace FaclCore.decide

def outcomeToSpec : Outcome → Facl.Outcome
  | .Granted => .granted
  | .NotGranted => .notGranted

def verdictToSpec : Verdict → Facl.Verdict
  | .Allow => .allow
  | .Deny => .deny

end FaclCore.decide
