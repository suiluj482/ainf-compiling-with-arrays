import Polara.Examples.Definitions
--import Polara.Embedding

open Tm Ty Const0 Const1 Const2

#eval (mainBlackScholes (Γ:=_) (n:=10)) |>.toAINF
#eval (mainBlackScholes (Γ:=_) (n:=10)) |>.toAINF.cse [] []
#eval (mainBlackScholes (Γ:=.) (n:=10)) |> norm |>.toAINF
#eval (mainBlackScholes (Γ:=.) (n:=10)) |> norm |>.toAINF.cse [] []

#eval IO.println ((mainBlackScholes (Γ:=.) (n:=10)) |> norm |>.toAINF)
#eval (fun _ => mainBlackScholes (n:=10)) |> norm |>.pp (0,0) |> IO.println

#eval (dense (Γ:=_) (n:=10) (m:=20)) |>.toAINF
#eval (dense (Γ:=_) (n:=10) (m:=20)) |>.toAINF.cse [] []
#eval (dense (Γ:=.) (n:=10) (m:=20)) |> norm |>.toAINF
#eval (dense (Γ:=.) (n:=10) (m:=20)) |> norm |>.toAINF.cse [] []

#eval (conv (Γ:=_) (n:=10) (m:=20)) |>.toAINF
#eval (conv (Γ:=.) (n:=10) (m:=20)) |> norm |>.toAINF
#eval (conv (Γ:=_) (n:=10) (m:=20)) |>.toAINF.cse [] []
#eval (conv (Γ:=.) (n:=10) (m:=20)) |> norm |>.toAINF.cse [] []

-- loop example
#eval loop1 5 (Γ:=_).toAINF
#eval (loop1 5 (Γ:=_).toAINF.cse [] [])

#eval IO.println <| (loop1 5 (Γ:=_).toAINF.cse [] []) |>.codegen id

-- foo example
#eval foo (n:=3).toAINF
#eval foo (n:=3).toAINF.cse [] []

-- four additions become three additions
#eval cseTest1 (Γ:=_).toAINF
#eval cseTest1 (Γ:=_).toAINF.cse [] []

-- two additions become one addition
#eval cseTest2 (Γ:=_).toAINF
#eval (cseTest2 (Γ:=_).toAINF.cse [] [])

-- two additions become one addition
#eval cseTest3 (Γ:=_).toAINF
#eval (cseTest3 (Γ:=_).toAINF.cse [] [])

-- egypt
#reduce egypt 1 (Γ:=_)
#reduce norm (egypt 1 (Γ:=.))

#eval (egypt 3 (Γ:=_)).toAINF
#eval (egypt 3 (Γ:=_)).toAINF.cse [] []
#eval (norm (egypt 3 (Γ:=.))).toAINF
#eval (norm (egypt 3 (Γ:=.))).toAINF.cse [] []

#eval (egypt 3 (Γ:=_)).toAINF
#eval (egypt 3 (Γ:=_)).toAINF.cse [] []
#eval (norm (fun Γ => egypt 3 (Γ:=Γ))).toAINF
#eval (norm (fun Γ => egypt 3 (Γ:=Γ))).toAINF.cse [] []
