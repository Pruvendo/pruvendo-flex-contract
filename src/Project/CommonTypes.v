Require Import UMLang.SolidityNotations2. 

Module trainContractTypes (xt: XTypesSig).

Import xt.

Definition XTokensType     := XInteger.
Definition WalletGramsType256 := XInteger.
Definition WalletGramsType128 := XInteger.
Definition XGrams := XInteger.
Definition XHandle := XMaybe . (*interesting*)
Definition XBytes := XHMap XInteger XInteger .
Definition TokenId := XInteger.
Definition RightId := XInteger.
Definition RightsType := XInteger .

End trainContractTypes.