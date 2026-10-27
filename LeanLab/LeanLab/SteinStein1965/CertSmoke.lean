import LeanLab.SteinStein1965.Certify

namespace LeanLab.SteinStein1965

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

certify_replay smoke89 (fun _ a => a) (List.replicate 65 0)

#print axioms smoke89

end LeanLab.SteinStein1965
