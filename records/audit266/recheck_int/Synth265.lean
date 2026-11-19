import PAG265
open PAG.Part265
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
#synth NonUnitalRing CornerLim
#synth Module ℂ CornerLim
#synth IsScalarTower ℂ CornerLim CornerLim
#synth SMulCommClass ℂ CornerLim CornerLim
#check @IsIdempotentElem.one
#check @IsIdempotentElem.map
