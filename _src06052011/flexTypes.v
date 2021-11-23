Require Import UMLang.BasicModuleTypes. 

Module flexTypes (xt: XTypesSig).

Import xt.

Definition XTokensType     := uint.
Definition WalletGramsType256 := uint.
Definition WalletGramsType128 := uint.
Definition XGrams := uint.
Definition XHandle := XMaybe . (*interesting*)
Definition XBytes := XHMap uint uint .
Definition TokenId := uint.
Definition RightId := uint.
Definition RightsType := uint .

End flexTypes.