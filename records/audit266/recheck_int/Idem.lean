import PAG265
open PAG.Part265
set_option synthInstance.maxHeartbeats 400000
example (a : PAG.Part258.Lvl) : IsIdempotentElem (ofCorner a 1) := IsIdempotentElem.one.map (ofCorner a)
